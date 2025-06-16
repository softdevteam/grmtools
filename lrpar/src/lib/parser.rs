#![allow(clippy::derive_partial_eq_without_eq)]
use std::{
    error::Error,
    fmt::{self, Debug, Display, Write as _},
    hash::Hash,
    marker::PhantomData,
    vec,
};

// Can be used on non-wasm32 but to avoid the dependency.
#[cfg(not(target_arch = "wasm32"))]
use std::time::{Duration, Instant};
#[cfg(target_arch = "wasm32")]
use web_time::{Duration, Instant};

use cactus::Cactus;
use cfgrammar::{RIdx, Span, TIdx, header::Value, span::Location, yacc::YaccGrammar};
use lrtable::{Action, StIdx, StateTable};
use num_traits::{AsPrimitive, PrimInt, Unsigned};
use proc_macro2::TokenStream;
use quote::quote;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use crate::{LexError, Lexeme, LexerTypes, NonStreamingLexer, cpctplus};

#[cfg(test)]
const RECOVERY_TIME_BUDGET: u64 = 60_000; // milliseconds
#[cfg(not(test))]
const RECOVERY_TIME_BUDGET: u64 = 500; // milliseconds

#[deprecated(
    since = "0.14.0",
    note = "Use the version of `Node` exported from your `lrpar_mod!`"
)]
pub type Node<T, S> = _deprecated_moved_::Node<T, S>;

#[doc(hidden)]
pub mod _deprecated_moved_ {
    use super::*;
    /// A generic parse tree.
    #[derive(Debug, Clone, PartialEq)]
    pub enum Node<LexemeT: Lexeme<StorageT>, StorageT> {
        /// Terminals store a single lexeme.
        Term { lexeme: LexemeT },
        /// Nonterminals reference a rule and have zero or more `Node`s as children.
        Nonterm {
            ridx: RIdx<StorageT>,
            nodes: Vec<Node<LexemeT, StorageT>>,
        },
    }
}

#[allow(deprecated)]
impl<LexemeT: Lexeme<StorageT>, StorageT: 'static + PrimInt + Unsigned> Node<LexemeT, StorageT>
where
    usize: AsPrimitive<StorageT>,
{
    /// Return a pretty-printed version of this node.
    pub fn pp(&self, grm: &YaccGrammar<StorageT>, input: &str) -> String {
        let mut st = vec![(0, self)]; // Stack of (indent level, node) pairs
        let mut s = String::new();
        while let Some((indent, e)) = st.pop() {
            for _ in 0..indent {
                s.push(' ');
            }
            match *e {
                Node::Term { lexeme } => {
                    let tidx = TIdx(lexeme.tok_id());
                    let tn = grm.token_name(tidx).unwrap();
                    let lt = &input[lexeme.span().start()..lexeme.span().end()];
                    writeln!(s, "{} {}", tn, lt).ok();
                }
                Node::Nonterm { ridx, ref nodes } => {
                    writeln!(s, "{}", grm.rule_name_str(ridx)).ok();
                    for x in nodes.iter().rev() {
                        st.push((indent + 1, x));
                    }
                }
            }
        }
        s
    }
}

type PStack<StorageT> = Vec<StIdx<StorageT>>; // Parse stack
type TokenCostFn<'a, StorageT> = &'a (dyn Fn(TIdx<StorageT>) -> u8 + 'a);
type ActionFn<'a, 'b, 'input, StorageT, LexerTypesT, ActionT, ParamT> = &'a dyn Fn(
    RIdx<StorageT>,
    &'b dyn NonStreamingLexer<'input, LexerTypesT>,
    Span,
    vec::Drain<AStackType<<LexerTypesT as LexerTypes>::LexemeT, ActionT>>,
    ParamT,
) -> ActionT;

#[derive(Debug)]
pub enum AStackType<LexemeT, ActionT> {
    ActionType(ActionT),
    Lexeme(LexemeT),
}

pub(super) struct Parser<
    'a,
    'b: 'a,
    'input: 'b,
    StorageT: 'static + Eq + Hash + PrimInt + Unsigned,
    LexerTypesT: LexerTypes<StorageT = StorageT>,
    ActionT: 'a,
    ParamT: Clone,
> where
    usize: AsPrimitive<StorageT>,
{
    rcvry_kind: RecoveryKind,
    pub(super) grm: &'a YaccGrammar<StorageT>,
    pub(super) token_cost: Box<TokenCostFn<'a, StorageT>>,
    pub(super) stable: &'a StateTable<StorageT>,
    lexer: &'b dyn NonStreamingLexer<'input, LexerTypesT>,
    // In the long term, we should remove the `lexemes` field entirely, as the `NonStreamingLexer` API is
    // powerful enough to allow us to incrementally obtain lexemes and buffer them when necessary.
    pub(super) lexemes: Vec<LexerTypesT::LexemeT>,
    actions: &'a [ActionFn<'a, 'b, 'input, LexerTypesT::StorageT, LexerTypesT, ActionT, ParamT>],
    param: ParamT,
}

impl<
    'a,
    'b: 'a,
    'input: 'b,
    StorageT: 'static + Debug + Hash + PrimInt + Unsigned,
    LexerTypesT: LexerTypes<StorageT = StorageT>,
    Node,
>
    Parser<
        'a,
        'b,
        'input,
        StorageT,
        LexerTypesT,
        Node,
        (
            &dyn Fn(LexerTypesT::LexemeT) -> Node,
            &dyn Fn(RIdx<StorageT>, Vec<Node>) -> Node,
        ),
    >
where
    usize: AsPrimitive<StorageT>,
{
    fn parse_map(
        rcvry_kind: RecoveryKind,
        grm: &YaccGrammar<StorageT>,
        token_cost: TokenCostFn<'a, StorageT>,
        stable: &StateTable<StorageT>,
        lexer: &'b dyn NonStreamingLexer<'input, LexerTypesT>,
        lexemes: Vec<LexerTypesT::LexemeT>,
        fterm: &'a dyn Fn(LexerTypesT::LexemeT) -> Node,
        fnonterm: &'a dyn Fn(RIdx<StorageT>, Vec<Node>) -> Node,
    ) -> (Option<Node>, Vec<LexParseError<StorageT, LexerTypesT>>) {
        for tidx in grm.iter_tidxs() {
            assert!(token_cost(tidx) > 0);
        }
        let mut actions: Vec<
            ActionFn<
                'a,
                'b,
                'input,
                StorageT,
                LexerTypesT,
                Node,
                (
                    &'a dyn Fn(LexerTypesT::LexemeT) -> Node,
                    &'a dyn Fn(RIdx<StorageT>, Vec<Node>) -> Node,
                ),
            >,
        > = Vec::new();
        actions.resize(usize::from(grm.prods_len()), &action_map);
        let psr = Parser {
            rcvry_kind,
            grm,
            token_cost: Box::new(token_cost),
            stable,
            lexer,
            lexemes,
            actions: actions.as_slice(),
            param: (fterm, fnonterm),
        };
        let mut pstack = vec![stable.start_state()];
        let mut astack = Vec::new();
        let mut errors = Vec::new();
        let mut spans = Vec::new();
        let accpt = psr.lr(0, &mut pstack, &mut astack, &mut errors, &mut spans);
        (accpt, errors)
    }
}

fn action_map<StorageT, LexerTypesT: LexerTypes, Node>(
    ridx: RIdx<StorageT>,
    _lexer: &dyn NonStreamingLexer<LexerTypesT>,
    _span: Span,
    astack: vec::Drain<AStackType<LexerTypesT::LexemeT, Node>>,
    param: (
        &dyn Fn(LexerTypesT::LexemeT) -> Node,
        &dyn Fn(RIdx<StorageT>, Vec<Node>) -> Node,
    ),
) -> Node
where
    usize: AsPrimitive<LexerTypesT::StorageT>,
    LexerTypesT::LexemeT: Lexeme<StorageT>,
{
    let (fterm, fnonterm) = param;
    let mut nodes = Vec::with_capacity(astack.len());
    for a in astack {
        nodes.push(match a {
            AStackType::ActionType(n) => n,
            AStackType::Lexeme(lexeme) => fterm(lexeme),
        });
    }
    fnonterm(ridx, nodes)
}

#[deprecated(
    since = "0.14.0",
    note = "Deprecated with `parse_generictree` there is no direct replacement, besides a custom action"
)]
#[allow(deprecated)]
/// The action which implements [`cfgrammar::yacc::YaccOriginalActionKind::GenericParseTree`].
/// Usually you should just use the action kind directly. But you can also call this from
/// within a custom action to return a generic parse tree with custom behavior.
pub fn action_generictree<StorageT, LexerTypesT: LexerTypes>(
    ridx: RIdx<StorageT>,
    _lexer: &dyn NonStreamingLexer<LexerTypesT>,
    _span: Span,
    astack: vec::Drain<AStackType<LexerTypesT::LexemeT, Node<LexerTypesT::LexemeT, StorageT>>>,
    _param: (),
) -> Node<LexerTypesT::LexemeT, StorageT>
where
    usize: AsPrimitive<LexerTypesT::StorageT>,
    LexerTypesT::LexemeT: Lexeme<StorageT>,
{
    let mut nodes = Vec::with_capacity(astack.len());
    for a in astack {
        nodes.push(match a {
            AStackType::ActionType(n) => n,
            AStackType::Lexeme(lexeme) => Node::Term { lexeme },
        });
    }
    Node::Nonterm { ridx, nodes }
}

impl<
    'a,
    'b: 'a,
    'input: 'b,
    StorageT: 'static + Debug + Eq + Hash + PrimInt + Unsigned,
    LexerTypesT: LexerTypes<StorageT = StorageT>,
    ActionT: 'a,
    ParamT: Clone,
> Parser<'a, 'b, 'input, StorageT, LexerTypesT, ActionT, ParamT>
where
    usize: AsPrimitive<StorageT>,
{
    fn parse_actions(
        rcvry_kind: RecoveryKind,
        grm: &'a YaccGrammar<StorageT>,
        token_cost: TokenCostFn<'a, StorageT>,
        stable: &'a StateTable<StorageT>,
        lexer: &'b dyn NonStreamingLexer<'input, LexerTypesT>,
        lexemes: Vec<LexerTypesT::LexemeT>,
        actions: &'a [ActionFn<'a, 'b, 'input, StorageT, LexerTypesT, ActionT, ParamT>],
        param: ParamT,
    ) -> (Option<ActionT>, Vec<LexParseError<StorageT, LexerTypesT>>) {
        for tidx in grm.iter_tidxs() {
            assert!(token_cost(tidx) > 0);
        }
        let psr = Parser {
            rcvry_kind,
            grm,
            token_cost: Box::new(token_cost),
            stable,
            lexer,
            lexemes,
            actions,
            param,
        };
        let mut pstack = vec![stable.start_state()];
        let mut astack = Vec::new();
        let mut errors = Vec::new();
        let mut spans = Vec::new();
        let accpt = psr.lr(0, &mut pstack, &mut astack, &mut errors, &mut spans);
        (accpt, errors)
    }

    /// Start parsing text at `laidx` (using the lexeme in `lexeme_prefix`, if it is not `None`,
    /// as the first lexeme) up to (but excluding) `end_laidx` (if it's specified). Parsing
    /// continues as long as possible (assuming that any errors encountered can be recovered from)
    /// unless `end_laidx` is `None`, at which point this function returns as soon as it
    /// encounters an error.
    ///
    /// Note that if `lexeme_prefix` is specified, `laidx` will still be incremented, and thus
    /// `end_laidx` *must* be set to `laidx + 1` in order that the parser doesn't skip the real
    /// lexeme at position `laidx`.
    ///
    /// Return `Some(value)` if the parse reached an accept state (i.e. all the input was consumed,
    /// possibly after making repairs) or `None` (i.e. some of the input was not consumed, even
    /// after possibly making repairs) otherwise.
    fn lr(
        &self,
        mut laidx: usize,
        pstack: &mut PStack<StorageT>,
        astack: &mut Vec<AStackType<LexerTypesT::LexemeT, ActionT>>,
        errors: &mut Vec<LexParseError<StorageT, LexerTypesT>>,
        spans: &mut Vec<Span>,
    ) -> Option<ActionT> {
        let mut recoverer = None;
        let mut recovery_budget = Duration::from_millis(RECOVERY_TIME_BUDGET);
        loop {
            debug_assert_eq!(astack.len(), spans.len());
            let stidx = *pstack.last().unwrap();
            let la_tidx = self.next_tidx(laidx);

            match self.stable.action(stidx, la_tidx) {
                Action::Reduce(pidx) => {
                    let ridx = self.grm.prod_to_rule(pidx);
                    let pop_idx = pstack.len() - self.grm.prod(pidx).len();

                    pstack.drain(pop_idx..);
                    let prior = *pstack.last().unwrap();
                    pstack.push(self.stable.goto(prior, ridx).unwrap());

                    let span = if spans.is_empty() {
                        Span::new(0, 0)
                    } else if pop_idx - 1 < spans.len() {
                        Span::new(spans[pop_idx - 1].start(), spans[spans.len() - 1].end())
                    } else {
                        Span::new(spans[spans.len() - 1].start(), spans[spans.len() - 1].end())
                    };
                    spans.truncate(pop_idx - 1);
                    spans.push(span);

                    let v = AStackType::ActionType(self.actions[usize::from(pidx)](
                        ridx,
                        self.lexer,
                        span,
                        astack.drain(pop_idx - 1..),
                        self.param.clone(),
                    ));
                    astack.push(v);
                }
                Action::Shift(state_id) => {
                    let la_lexeme = self.next_lexeme(laidx);
                    pstack.push(state_id);
                    astack.push(AStackType::Lexeme(la_lexeme));

                    spans.push(la_lexeme.span());
                    laidx += 1;
                }
                Action::Accept => {
                    debug_assert_eq!(la_tidx, self.grm.eof_token_idx());
                    debug_assert_eq!(astack.len(), 1);
                    match astack.drain(..).next().unwrap() {
                        AStackType::ActionType(v) => return Some(v),
                        _ => unreachable!(),
                    }
                }
                Action::Error => {
                    if recoverer.is_none() {
                        recoverer = Some(match self.rcvry_kind {
                            RecoveryKind::CPCTPlus => cpctplus::recoverer(self),
                            RecoveryKind::None => {
                                let la_lexeme = self.next_lexeme(laidx);
                                errors.push(
                                    ParseError {
                                        stidx,
                                        lexeme: la_lexeme,
                                        repairs: vec![],
                                    }
                                    .into(),
                                );
                                return None;
                            }
                        });
                    }

                    let before = Instant::now();
                    let finish_by = before + recovery_budget;
                    let (new_laidx, repairs) = recoverer
                        .as_ref()
                        .unwrap()
                        .as_ref()
                        .recover(finish_by, self, laidx, pstack, astack, spans);
                    let after = Instant::now();
                    recovery_budget = recovery_budget
                        .checked_sub(after - before)
                        .unwrap_or_else(|| Duration::new(0, 0));
                    let keep_going = !repairs.is_empty();
                    let la_lexeme = self.next_lexeme(laidx);
                    errors.push(
                        ParseError {
                            stidx,
                            lexeme: la_lexeme,
                            repairs,
                        }
                        .into(),
                    );
                    if !keep_going {
                        return None;
                    }
                    laidx = new_laidx;
                }
            }
        }
    }

    /// Parse from `laidx` up to (but excluding) `end_laidx` mutating `pstack` as parsing occurs.
    /// Returns the index of the token it parsed up to (by definition <= end_laidx: can be less if
    /// the input is < end_laidx, or if an error is encountered). Does not do any form of error
    /// recovery.
    pub(super) fn lr_upto(
        &self,
        lexeme_prefix: Option<LexerTypesT::LexemeT>,
        mut laidx: usize,
        end_laidx: usize,
        pstack: &mut PStack<StorageT>,
        astack: &mut Option<&mut Vec<AStackType<LexerTypesT::LexemeT, ActionT>>>,
        spans: &mut Option<&mut Vec<Span>>,
    ) -> usize {
        assert!(lexeme_prefix.is_none() || end_laidx == laidx + 1);
        while laidx != end_laidx && laidx <= self.lexemes.len() {
            let stidx = *pstack.last().unwrap();
            let la_tidx = if let Some(l) = lexeme_prefix {
                TIdx(l.tok_id())
            } else {
                self.next_tidx(laidx)
            };

            match self.stable.action(stidx, la_tidx) {
                Action::Reduce(pidx) => {
                    let ridx = self.grm.prod_to_rule(pidx);
                    let pop_idx = pstack.len() - self.grm.prod(pidx).len();
                    if let Some(ref mut astack_uw) = *astack {
                        if let Some(ref mut spans_uw) = *spans {
                            let span = if spans_uw.is_empty() {
                                Span::new(0, 0)
                            } else if pop_idx - 1 < spans_uw.len() {
                                Span::new(
                                    spans_uw[pop_idx - 1].start(),
                                    spans_uw[spans_uw.len() - 1].end(),
                                )
                            } else {
                                Span::new(
                                    spans_uw[spans_uw.len() - 1].start(),
                                    spans_uw[spans_uw.len() - 1].end(),
                                )
                            };
                            spans_uw.truncate(pop_idx - 1);
                            spans_uw.push(span);

                            let v = AStackType::ActionType(self.actions[usize::from(pidx)](
                                ridx,
                                self.lexer,
                                span,
                                astack_uw.drain(pop_idx - 1..),
                                self.param.clone(),
                            ));
                            astack_uw.push(v);
                        } else {
                            unreachable!();
                        }
                    }

                    pstack.drain(pop_idx..);
                    let prior = *pstack.last().unwrap();
                    pstack.push(self.stable.goto(prior, ridx).unwrap());
                }
                Action::Shift(state_id) => {
                    if let Some(ref mut astack_uw) = *astack {
                        if let Some(spans_uw) = spans {
                            let la_lexeme = if let Some(l) = lexeme_prefix {
                                l
                            } else {
                                self.next_lexeme(laidx)
                            };
                            astack_uw.push(AStackType::Lexeme(la_lexeme));
                            spans_uw.push(la_lexeme.span());
                        }
                    }
                    pstack.push(state_id);
                    laidx += 1;
                }
                Action::Accept => {
                    break;
                }
                Action::Error => {
                    break;
                }
            }
        }
        laidx
    }

    /// Return a `Lexeme` for the next lemexe (if `laidx` == `self.lexemes.len()` this will be
    /// a lexeme constructed to look as if contains the EOF token).
    pub(super) fn next_lexeme(&self, laidx: usize) -> LexerTypesT::LexemeT {
        let llen = self.lexemes.len();
        debug_assert!(laidx <= llen);
        if laidx < llen {
            self.lexemes[laidx]
        } else {
            // We have to artificially construct a Lexeme for the EOF lexeme.
            let last_la_end = if llen == 0 {
                0
            } else {
                debug_assert!(laidx > 0);
                let last_la = self.lexemes[laidx - 1];
                last_la.span().end()
            };

            Lexeme::new_faulty(
                StorageT::from(u32::from(self.grm.eof_token_idx())).unwrap(),
                last_la_end,
                0,
            )
        }
    }

    /// Return the `TIdx` of the next lexeme (if `laidx` == `self.lexemes.len()` this will be the
    /// EOF `TIdx`).
    pub(super) fn next_tidx(&self, laidx: usize) -> TIdx<StorageT> {
        let ll = self.lexemes.len();
        debug_assert!(laidx <= ll);
        if laidx < ll {
            TIdx(self.lexemes[laidx].tok_id())
        } else {
            self.grm.eof_token_idx()
        }
    }

    /// Start parsing text at `laidx` (using the lexeme in `lexeme_prefix`, if it is not `None`,
    /// as the first lexeme) up to (but excluding) `end_laidx`. If an error is encountered, parsing
    /// immediately terminates (without recovery).
    ///
    /// Note that if `lexeme_prefix` is specified, `laidx` will still be incremented, and thus
    /// `end_laidx` *must* be set to `laidx + 1` in order that the parser doesn't skip the real
    /// lexeme at position `laidx`.
    #[allow(deprecated)]
    pub(super) fn lr_cactus(
        &self,
        lexeme_prefix: Option<LexerTypesT::LexemeT>,
        mut laidx: usize,
        end_laidx: usize,
        mut pstack: Cactus<StIdx<StorageT>>,
        tstack: &mut Option<&mut Vec<Node<LexerTypesT::LexemeT, StorageT>>>,
    ) -> (usize, Cactus<StIdx<StorageT>>) {
        assert!(lexeme_prefix.is_none() || end_laidx == laidx + 1);
        while laidx != end_laidx {
            let stidx = *pstack.val().unwrap();
            let la_tidx = if let Some(l) = lexeme_prefix {
                TIdx(l.tok_id())
            } else {
                self.next_tidx(laidx)
            };

            match self.stable.action(stidx, la_tidx) {
                Action::Reduce(pidx) => {
                    let ridx = self.grm.prod_to_rule(pidx);
                    let pop_num = self.grm.prod(pidx).len();
                    if let Some(ref mut tstack_uw) = *tstack {
                        let nodes = tstack_uw
                            .drain(pstack.len() - pop_num - 1..)
                            .collect::<Vec<Node<LexerTypesT::LexemeT, StorageT>>>();
                        tstack_uw.push(Node::Nonterm { ridx, nodes });
                    }

                    for _ in 0..pop_num {
                        pstack = pstack.parent().unwrap();
                    }
                    let prior = *pstack.val().unwrap();
                    pstack = pstack.child(self.stable.goto(prior, ridx).unwrap());
                }
                Action::Shift(state_id) => {
                    if let Some(ref mut tstack_uw) = *tstack {
                        let la_lexeme = if let Some(l) = lexeme_prefix {
                            l
                        } else {
                            self.next_lexeme(laidx)
                        };
                        tstack_uw.push(Node::Term { lexeme: la_lexeme });
                    }
                    pstack = pstack.child(state_id);
                    laidx += 1;
                }
                Action::Accept => {
                    debug_assert_eq!(la_tidx, self.grm.eof_token_idx());
                    if let Some(ref tstack_uw) = *tstack {
                        debug_assert_eq!(tstack_uw.len(), 1);
                    }
                    break;
                }
                Action::Error => {
                    break;
                }
            }
        }
        (laidx, pstack)
    }
}

pub(super) trait Recoverer<
    StorageT: 'static + Debug + Hash + PrimInt + Unsigned,
    LexerTypesT: LexerTypes<StorageT = StorageT>,
    ActionT,
    ParamT: Clone,
> where
    usize: AsPrimitive<StorageT>,
{
    fn recover(
        &self,
        finish_by: Instant,
        parser: &Parser<StorageT, LexerTypesT, ActionT, ParamT>,
        in_laidx: usize,
        in_pstack: &mut PStack<StorageT>,
        astack: &mut Vec<AStackType<LexerTypesT::LexemeT, ActionT>>,
        spans: &mut Vec<Span>,
    ) -> (usize, Vec<Vec<ParseRepair<LexerTypesT::LexemeT, StorageT>>>);
}

/// What recovery algorithm should be used when a syntax error is encountered?
#[derive(Clone, Copy, Debug)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[non_exhaustive]
pub enum RecoveryKind {
    /// The CPCT+ algorithm from Diekmann/Tratt "Don't Panic! Better, Fewer, Syntax Errors for LR
    /// Parsers".
    CPCTPlus,
    /// Don't use error recovery: return as soon as the first syntax error is encountered.
    None,
}

impl TryFrom<RecoveryKind> for Value<Location> {
    type Error = cfgrammar::header::HeaderError<Location>;
    fn try_from(rk: RecoveryKind) -> Result<Value<Location>, Self::Error> {
        use cfgrammar::{
            Location,
            header::{Namespaced, Setting},
        };
        let from_loc = Location::Other("From<RecoveryKind>".to_string());
        Ok(match rk {
            RecoveryKind::CPCTPlus => Value::Setting(Setting::Unitary(Namespaced {
                namespace: Some(("RecoveryKind".to_string(), from_loc.clone())),
                member: ("CPCTPlus".to_string(), from_loc.clone()),
            })),
            RecoveryKind::None => Value::Setting(Setting::Unitary(Namespaced {
                namespace: Some(("RecoveryKind".to_string(), from_loc.clone())),
                member: ("None".to_string(), from_loc.clone()),
            })),
        })
    }
}

impl TryFrom<&Value<Location>> for RecoveryKind {
    type Error = cfgrammar::header::HeaderError<Location>;
    fn try_from(rk: &Value<Location>) -> Result<RecoveryKind, Self::Error> {
        use cfgrammar::header::{HeaderError, HeaderErrorKind, Namespaced, Setting};

        match rk {
            Value::Flag(_, loc) => Err(HeaderError {
                kind: HeaderErrorKind::ConversionError(
                    "RecoveryKind",
                    "Cannot convert boolean to RecoveryKind",
                ),
                locations: vec![loc.clone()],
            }),
            Value::Setting(Setting::Num(_, loc)) => Err(HeaderError {
                kind: HeaderErrorKind::ConversionError(
                    "RecoveryKind",
                    "Cannot convert number to RecoveryKind",
                ),
                locations: vec![loc.clone()],
            }),
            Value::Setting(Setting::String(_, loc)) => Err(HeaderError {
                kind: HeaderErrorKind::ConversionError(
                    "RecoveryKind",
                    "Cannot convert string to RecoveryKind",
                ),
                locations: vec![loc.clone()],
            }),
            Value::Setting(Setting::Unitary(Namespaced {
                namespace,
                member: (kind, kind_loc),
            })) => {
                match namespace {
                    Some((ns, loc)) if ns.to_lowercase() != "recoverykind" => {
                        return Err(HeaderError {
                            kind: HeaderErrorKind::ConversionError(
                                "RecoveryKind",
                                "Unknown namespace",
                            ),
                            locations: vec![loc.clone()],
                        });
                    }
                    _ => {}
                }
                match kind.to_lowercase().as_ref() {
                    "cpctplus" => Ok(RecoveryKind::CPCTPlus),
                    "none" => Ok(RecoveryKind::None),
                    _ => Err(HeaderError {
                        kind: HeaderErrorKind::ConversionError("RecoveryKind", "Unknown variant"),
                        locations: vec![kind_loc.clone()],
                    }),
                }
            }
            Value::Setting(Setting::Constructor {
                ctor: _,
                arg:
                    Namespaced {
                        namespace: _,
                        member: (_, arg_loc),
                    },
            }) => Err(HeaderError {
                kind: HeaderErrorKind::ConversionError(
                    "RecoveryKind",
                    "Cannot convert constructor to RecoveryKind",
                ),
                locations: vec![arg_loc.clone()],
            }),
        }
    }
}

impl quote::ToTokens for RecoveryKind {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        tokens.extend(match *self {
            RecoveryKind::CPCTPlus => quote!(::lrpar::RecoveryKind::CPCTPlus),
            RecoveryKind::None => quote!(::lrpar::RecoveryKind::None),
        })
    }
}

/// A lexing or parsing error. Although the two are quite distinct in terms of what can be reported
/// to users, both can (at least conceptually) occur at any point of the intertwined lexing/parsing
/// process.
#[derive(Debug)]
pub enum LexParseError<
    StorageT: 'static + Debug + Hash + PrimInt + Unsigned,
    LexerTypesT: LexerTypes<StorageT = StorageT>,
> where
    usize: AsPrimitive<StorageT>,
{
    LexError(LexerTypesT::LexErrorT),
    ParseError(ParseError<LexerTypesT::LexemeT, StorageT>),
}

impl<StorageT: Debug + Hash + PrimInt + Unsigned, LexerTypesT: LexerTypes<StorageT = StorageT>>
    LexParseError<StorageT, LexerTypesT>
where
    usize: AsPrimitive<StorageT>,
{
    /// A pretty-printer of a lexer/parser error. This isn't suitable for all purposes, but it's
    /// often good enough. The output format is not guaranteed to be stable but is likely to be of
    /// the form:
    ///
    /// ```text
    /// Parsing error at line 3 column 8. Repair sequences found:
    ///   1: Insert ID
    ///   2: Delete +, Shift 3
    /// ```
    ///
    /// If you are using the compile-time parse system, your `grm_y` module exposes a suitable
    /// [`epp`](../ctbuilder/struct.CTParserBuilder.html#method.process_file) function; if you are
    /// using the run-time system,
    /// [`YaccGrammar`](../../cfgrammar/yacc/grammar/struct.YaccGrammar.html) exposes a suitable
    /// [`epp`](../../cfgrammar/yacc/grammar/struct.YaccGrammar.html#method.token_epp) function,
    /// though you will have to wrap it in a closure e.g. `&|t| grm.token_epp(t)`.
    pub fn pp<'a>(
        &self,
        lexer: &dyn NonStreamingLexer<LexerTypesT>,
        epp: &dyn Fn(TIdx<StorageT>) -> Option<&'a str>,
    ) -> String {
        match self {
            LexParseError::LexError(e) => {
                let ((line, col), _) = lexer.line_col(e.span());
                format!("Lexing error at line {} column {}.", line, col)
            }
            LexParseError::ParseError(e) => {
                let ((line, col), _) = lexer.line_col(e.lexeme().span());
                let mut out = format!("Parsing error at line {} column {}.", line, col);
                let repairs_len = e.repairs().len();
                if repairs_len == 0 {
                    out.push_str(" No repair sequences found.");
                } else {
                    out.push_str(" Repair sequences found:");
                    for (i, rs) in e.repairs().iter().enumerate() {
                        let padding = ((repairs_len as f64).log10() as usize)
                            - (((i + 1) as f64).log10() as usize)
                            + 1;
                        write!(out, "\n  {}{}: ", " ".repeat(padding), i + 1).ok();
                        let mut rs_out = Vec::new();

                        // Merge together Deletes iff they are consecutive (if they are separated
                        // by even a single character, they will not be merged).
                        let mut i = 0;
                        while i < rs.len() {
                            match rs[i] {
                                ParseRepair::Delete(l) => {
                                    let mut j = i + 1;
                                    let mut last_end = l.span().end();
                                    while j < rs.len() {
                                        if let ParseRepair::Delete(next_l) = rs[j] {
                                            if next_l.span().start() == last_end {
                                                last_end = next_l.span().end();
                                                j += 1;
                                                continue;
                                            }
                                        }
                                        break;
                                    }
                                    let t = &lexer
                                        .span_str(Span::new(l.span().start(), last_end))
                                        .replace('\n', "\\n");
                                    rs_out.push(format!("Delete {}", t));
                                    i = j;
                                }
                                ParseRepair::Insert(tidx) => {
                                    rs_out.push(format!("Insert {}", epp(tidx).unwrap()));
                                    i += 1;
                                }
                                ParseRepair::Shift(l) => {
                                    let t = &lexer.span_str(l.span()).replace('\n', "\\n");
                                    rs_out.push(format!("Shift {}", t));
                                    i += 1;
                                }
                            }
                        }

                        out.push_str(&rs_out.join(", "));
                    }
                }
                out
            }
        }
    }
}

impl<
    StorageT: 'static + Debug + Hash + PrimInt + Unsigned,
    LexerTypesT: LexerTypes<StorageT = StorageT>,
> fmt::Display for LexParseError<StorageT, LexerTypesT>
where
    usize: AsPrimitive<StorageT>,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            LexParseError::LexError(ref e) => Display::fmt(e, f),
            LexParseError::ParseError(ref e) => Display::fmt(e, f),
        }
    }
}

impl<
    StorageT: 'static + Debug + Hash + PrimInt + Unsigned,
    LexerTypesT: LexerTypes<StorageT = StorageT>,
> Error for LexParseError<StorageT, LexerTypesT>
where
    usize: AsPrimitive<StorageT>,
{
}

impl<
    StorageT: 'static + Debug + Hash + PrimInt + Unsigned,
    LexerTypesT: LexerTypes<StorageT = StorageT, LexErrorT = T>,
    T: LexError,
> From<T> for LexParseError<StorageT, LexerTypesT>
where
    usize: AsPrimitive<StorageT>,
{
    fn from(err: T) -> LexParseError<StorageT, LexerTypesT> {
        LexParseError::LexError(err)
    }
}

impl<
    StorageT: 'static + Debug + Hash + PrimInt + Unsigned,
    LexerTypesT: LexerTypes<StorageT = StorageT>,
> From<ParseError<LexerTypesT::LexemeT, StorageT>> for LexParseError<StorageT, LexerTypesT>
where
    usize: AsPrimitive<StorageT>,
{
    fn from(
        err: ParseError<LexerTypesT::LexemeT, StorageT>,
    ) -> LexParseError<StorageT, LexerTypesT> {
        LexParseError::ParseError(err)
    }
}

/// A run-time parser builder.
pub struct RTParserBuilder<
    'a,
    StorageT: 'static + Eq + Debug + Hash + PrimInt + Unsigned,
    LexerTypesT: LexerTypes<StorageT = StorageT>,
> where
    usize: AsPrimitive<StorageT>,
{
    grm: &'a YaccGrammar<StorageT>,
    stable: &'a StateTable<StorageT>,
    recoverer: RecoveryKind,
    term_costs: &'a dyn Fn(TIdx<StorageT>) -> u8,
    phantom: PhantomData<(StorageT, LexerTypesT)>,
}

impl<
    'a,
    StorageT: 'static + Debug + Hash + PrimInt + Unsigned,
    LexerTypesT: LexerTypes<StorageT = StorageT>,
> RTParserBuilder<'a, StorageT, LexerTypesT>
where
    usize: AsPrimitive<StorageT>,
{
    /// Create a new run-time parser from a `YaccGrammar`, and a `StateTable`.
    pub fn new(grm: &'a YaccGrammar<StorageT>, stable: &'a StateTable<StorageT>) -> Self {
        RTParserBuilder {
            grm,
            stable,
            recoverer: RecoveryKind::CPCTPlus,
            term_costs: &|_| 1,
            phantom: PhantomData,
        }
    }

    /// Set the recoverer for this parser to `rk`.
    pub fn recoverer(mut self, rk: RecoveryKind) -> Self {
        self.recoverer = rk;
        self
    }

    pub fn term_costs(mut self, f: &'a dyn Fn(TIdx<StorageT>) -> u8) -> Self {
        self.term_costs = f;
        self
    }

    #[deprecated(
        since = "0.14.0",
        note = "Use `parse_map` to return a `Node` from your `lrpar_mod!` instead"
    )]
    #[allow(deprecated)]
    /// Parse input, and (if possible) return a generic parse tree. See the arguments for
    /// [`parse_actions`](#method.parse_actions) for more details about the return value.
    pub fn parse_generictree(
        &self,
        lexer: &dyn NonStreamingLexer<LexerTypesT>,
    ) -> (
        Option<Node<LexerTypesT::LexemeT, StorageT>>,
        Vec<LexParseError<StorageT, LexerTypesT>>,
    ) {
        self.parse_map(lexer, &|lexeme| Node::Term { lexeme }, &|ridx, nodes| {
            Node::Nonterm { ridx, nodes }
        })
    }

    /// Parse input, and (if possible) return a generic parse tree. See the arguments for
    /// [`parse_actions`](#method.parse_actions) for more details about the return value.
    pub fn parse_map<Node>(
        &self,
        lexer: &dyn NonStreamingLexer<LexerTypesT>,
        fterm: &dyn Fn(LexerTypesT::LexemeT) -> Node,
        fnonterm: &dyn Fn(RIdx<StorageT>, Vec<Node>) -> Node,
    ) -> (Option<Node>, Vec<LexParseError<StorageT, LexerTypesT>>) {
        let mut lexemes = vec![];
        for e in lexer.iter().collect::<Vec<_>>() {
            match e {
                Ok(l) => lexemes.push(l),
                Err(e) => return (None, vec![e.into()]),
            }
        }
        Parser::<
            StorageT,
            LexerTypesT,
            Node,
            (
                &dyn Fn(LexerTypesT::LexemeT) -> Node,
                &dyn Fn(RIdx<StorageT>, Vec<Node>) -> Node,
            ),
        >::parse_map(
            self.recoverer,
            self.grm,
            self.term_costs,
            self.stable,
            lexer,
            lexemes,
            fterm,
            fnonterm,
        )
    }

    #[deprecated(since = "0.14.0", note = "Use `parse_map` instead")]
    /// Parse input, returning any errors found. See the arguments for
    /// [`parse_actions`](#method.parse_actions) for more details about the return value.
    pub fn parse_noaction(
        &self,
        lexer: &dyn NonStreamingLexer<LexerTypesT>,
    ) -> Vec<LexParseError<StorageT, LexerTypesT>> {
        self.parse_map(lexer, &|_| (), &|_, _| ()).1
    }

    /// Parse input, execute actions, and return the associated value (if possible) and/or any
    /// lexing/parsing errors encountered. Note that the two parts of the (value, errors) return
    /// pair are entirely independent: one can encounter errors without a value being produced
    /// (`None, [...]`), errors and a value (`Some(...), [...]`), as well as a value and no errors
    /// (`Some(...), []`). Errors are sorted by the position they were found in the input and can
    /// be a mix of lexing and parsing errors.
    pub fn parse_actions<'b: 'a, 'input: 'b, ActionT: 'a, ParamT: Clone>(
        &self,
        lexer: &'b dyn NonStreamingLexer<'input, LexerTypesT>,
        actions: &'a [ActionFn<'a, 'b, 'input, StorageT, LexerTypesT, ActionT, ParamT>],
        param: ParamT,
    ) -> (Option<ActionT>, Vec<LexParseError<StorageT, LexerTypesT>>) {
        let mut lexemes = vec![];
        for e in lexer.iter().collect::<Vec<_>>() {
            match e {
                Ok(l) => lexemes.push(l),
                Err(e) => return (None, vec![e.into()]),
            }
        }
        Parser::parse_actions(
            self.recoverer,
            self.grm,
            self.term_costs,
            self.stable,
            lexer,
            lexemes,
            actions,
            param,
        )
    }
}

/// After a parse error is encountered, the parser attempts to find a way of recovering. Each entry
/// in the sequence of repairs is represented by a `ParseRepair`.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum ParseRepair<LexemeT: Lexeme<StorageT>, StorageT: Hash> {
    /// Insert a `Symbol::Token`.
    Insert(TIdx<StorageT>),
    /// Delete a symbol.
    Delete(LexemeT),
    /// Shift a symbol.
    Shift(LexemeT),
}

/// Records a single parse error.
#[derive(Clone, Debug, PartialEq)]
pub struct ParseError<LexemeT: Lexeme<StorageT>, StorageT: Hash> {
    stidx: StIdx<StorageT>,
    lexeme: LexemeT,
    repairs: Vec<Vec<ParseRepair<LexemeT, StorageT>>>,
}

impl<LexemeT: Lexeme<StorageT>, StorageT: Debug + Hash> Display for ParseError<LexemeT, StorageT> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Parse error at lexeme {:?}", self.lexeme)
    }
}

impl<LexemeT: Lexeme<StorageT>, StorageT: Debug + Hash> Error for ParseError<LexemeT, StorageT> {}

impl<LexemeT: Lexeme<StorageT>, StorageT: Hash + PrimInt + Unsigned> ParseError<LexemeT, StorageT> {
    /// Return the state table index where this error was detected.
    pub fn stidx(&self) -> StIdx<StorageT> {
        self.stidx
    }

    /// Return the lexeme where this error was detected.
    pub fn lexeme(&self) -> &LexemeT {
        &self.lexeme
    }

    /// Return the repairs found that would fix this error. Note that there are infinite number of
    /// possible repairs for any error, so this is by definition a (finite) subset.
    pub fn repairs(&self) -> &Vec<Vec<ParseRepair<LexemeT, StorageT>>> {
        &self.repairs
    }
}

#[cfg(test)]
pub(crate) mod test {
    use std::collections::HashMap;

    use cfgrammar::{
        Span,
        yacc::{YaccGrammar, YaccKind, YaccOriginalActionKind},
    };
    use lrtable::{Minimiser, from_yacc};
    use num_traits::ToPrimitive;
    use regex::Regex;

    use super::*;
    use crate::{
        Lexeme, Lexer,
        test_utils::{TestLexError, TestLexeme, TestLexerTypes},
    };

    #[allow(deprecated)]
    pub(crate) fn do_parse<'input>(
        rcvry_kind: RecoveryKind,
        lexs: &str,
        grms: &str,
        input: &'input str,
    ) -> (
        YaccGrammar<u16>,
        SmallLexer<'input>,
        Result<
            Node<TestLexeme, u16>,
            (
                Option<Node<TestLexeme, u16>>,
                Vec<LexParseError<u16, TestLexerTypes>>,
            ),
        >,
    ) {
        do_parse_with_costs(rcvry_kind, lexs, grms, input, &HashMap::new())
    }

    #[allow(deprecated)]
    fn do_parse_with_costs<'input>(
        rcvry_kind: RecoveryKind,
        lexs: &str,
        grms: &str,
        input: &'input str,
        costs: &HashMap<&str, u8>,
    ) -> (
        YaccGrammar<u16>,
        SmallLexer<'input>,
        Result<
            Node<TestLexeme, u16>,
            (
                Option<Node<TestLexeme, u16>>,
                Vec<LexParseError<u16, TestLexerTypes>>,
            ),
        >,
    ) {
        let grm = YaccGrammar::<u16>::new_with_storaget(
            YaccKind::Original(YaccOriginalActionKind::GenericParseTree),
            grms,
        )
        .unwrap();
        let (_, stable) = from_yacc(&grm, Minimiser::Pager).unwrap();
        let rule_ids = grm
            .tokens_map()
            .iter()
            .map(|(&n, &i)| (n.to_owned(), u32::from(i).to_u16().unwrap()))
            .collect();
        let lexer_rules = small_lexer(lexs, rule_ids);
        let lexemes = small_lex(lexer_rules, input);
        let lexer = SmallLexer { lexemes, s: input };
        let costs_tidx = costs
            .iter()
            .map(|(k, v)| (grm.token_idx(k).unwrap(), v))
            .collect::<HashMap<_, _>>();
        let (r, errs) = RTParserBuilder::new(&grm, &stable)
            .recoverer(rcvry_kind)
            .term_costs(&|tidx| **costs_tidx.get(&tidx).unwrap_or(&&1))
            .parse_generictree(&lexer);
        if let Some(node) = r {
            if errs.is_empty() {
                (grm, lexer, Ok(node))
            } else {
                (grm, lexer, Err((Some(node), errs)))
            }
        } else {
            (grm, lexer, Err((None, errs)))
        }
    }

    fn check_parse_output(lexs: &str, grms: &str, input: &str, expected: &str) {
        let (grm, _, pt) = do_parse(RecoveryKind::CPCTPlus, lexs, grms, input);
        assert_eq!(expected, pt.unwrap().pp(&grm, input));
    }

    // SmallLexer is our highly simplified version of lrlex (allowing us to avoid having to have
    // lrlex as a dependency of lrpar). The format is the same as lrlex *except*:
    //   * The initial "%%" isn't needed, and only "'" is valid as a rule name delimiter.
    //   * "Unnamed" rules aren't allowed (e.g. you can't have a rule which discards whitespaces).
    pub(crate) struct SmallLexer<'input> {
        lexemes: Vec<TestLexeme>,
        s: &'input str,
    }

    impl Lexer<TestLexerTypes> for SmallLexer<'_> {
        fn iter<'a>(&'a self) -> Box<dyn Iterator<Item = Result<TestLexeme, TestLexError>> + 'a> {
            Box::new(self.lexemes.iter().map(|x| Ok(*x)))
        }
    }

    impl<'input> NonStreamingLexer<'input, TestLexerTypes> for SmallLexer<'input> {
        fn span_str(&self, span: Span) -> &'input str {
            &self.s[span.start()..span.end()]
        }

        fn span_lines_str(&self, _: Span) -> &'input str {
            unreachable!();
        }

        fn line_col(&self, _: Span) -> ((usize, usize), (usize, usize)) {
            unreachable!();
        }
    }

    fn small_lexer(lexs: &str, ids_map: HashMap<String, u16>) -> Vec<(u16, Regex)> {
        let mut rules = Vec::new();
        for l in lexs.split('\n').map(|x| x.trim()).filter(|x| !x.is_empty()) {
            assert!(l.rfind('\'') == Some(l.len() - 1));
            let i = l[..l.len() - 1].rfind('\'').unwrap();
            let name = &l[i + 1..l.len() - 1];
            let re = &l[..i - 1].trim();
            rules.push((
                ids_map[name],
                Regex::new(&format!("\\A(?:{})", re)).unwrap(),
            ));
        }
        rules
    }

    fn small_lex(rules: Vec<(u16, Regex)>, input: &str) -> Vec<TestLexeme> {
        let mut lexemes = vec![];
        let mut i = 0;
        while i < input.len() {
            let mut longest = 0; // Length of the longest match
            let mut longest_tok_id = 0; // This is only valid iff longest != 0
            for (tok_id, r) in rules.iter() {
                if let Some(m) = r.find(&input[i..]) {
                    let len = m.end();
                    if len > longest {
                        longest = len;
                        longest_tok_id = *tok_id;
                    }
                }
            }
            assert!(longest > 0);
            lexemes.push(Lexeme::new(longest_tok_id, i, longest));
            i += longest;
        }
        lexemes
    }

    #[test]
    fn simple_parse() {
        // From p4 of https://www.cs.umd.edu/class/spring2014/cmsc430/lectures/lec07.pdf
        check_parse_output(
            "[a-zA-Z_] 'ID'
             \\+ '+'",
            "
%start E
%%
E: T '+' E
 | T;
T: 'ID';
",
            "a+b",
            "E
 T
  ID a
 + +
 E
  T
   ID b
",
        );
    }

    #[test]
    fn parse_empty_rules() {
        let lexs = "[a-zA-Z_] 'ID'";
        let grms = "%start S
%%
S: L;
L: 'ID'
 | ;
";
        check_parse_output(
            lexs, grms, "", "S
 L
",
        );

        check_parse_output(
            lexs,
            grms,
            "x",
            "S
 L
  ID x
",
        );
    }

    #[test]
    fn recursive_parse() {
        let lexs = "\\+ '+'
                    \\* '*'
                    [0-9]+ 'INT'";
        let grms = "%start Expr
%%
Expr : Expr '+' Term | Term;
Term : Term '*' Factor | Factor;
Factor : 'INT';";

        check_parse_output(
            lexs,
            grms,
            "2+3*4",
            "Expr
 Expr
  Term
   Factor
    INT 2
 + +
 Term
  Term
   Factor
    INT 3
  * *
  Factor
   INT 4
",
        );
        check_parse_output(
            lexs,
            grms,
            "2*3+4",
            "Expr
 Expr
  Term
   Term
    Factor
     INT 2
   * *
   Factor
    INT 3
 + +
 Term
  Factor
   INT 4
",
        );
    }

    #[test]
    fn parse_error() {
        let lexs = "\\( '('
                    \\) ')'
                    [a-zA-Z_][a-zA-Z_0-9]* 'ID'";
        let grms = "%start Call
%%
Call: 'ID' '(' ')';";

        check_parse_output(
            lexs,
            grms,
            "f()",
            "Call
 ID f
 ( (
 ) )
",
        );

        let (grm, _, pr) = do_parse(RecoveryKind::CPCTPlus, lexs, grms, "f(");
        let (_, errs) = pr.unwrap_err();
        assert_eq!(errs.len(), 1);
        let err_tok_id = usize::from(grm.eof_token_idx()).to_u16().unwrap();
        match &errs[0] {
            LexParseError::ParseError(e) => {
                assert_eq!(e.lexeme(), &Lexeme::new_faulty(err_tok_id, 2, 0));
                assert!(e.lexeme().faulty());
            }
            _ => unreachable!(),
        }

        let (grm, _, pr) = do_parse(RecoveryKind::CPCTPlus, lexs, grms, "f(f(");
        let (_, errs) = pr.unwrap_err();
        assert_eq!(errs.len(), 1);
        let err_tok_id = usize::from(grm.token_idx("ID").unwrap()).to_u16().unwrap();
        match &errs[0] {
            LexParseError::ParseError(e) => {
                assert_eq!(e.lexeme(), &Lexeme::new(err_tok_id, 2, 1));
                assert!(!e.lexeme().faulty());
            }
            _ => unreachable!(),
        }
    }

    #[test]
    fn test_parse_map() {
        #[derive(PartialEq, Debug)]
        enum TestParseMap<'a> {
            Term(&'a str, &'a str),
            NonTerm(&'a str, Vec<TestParseMap<'a>>),
        }
        let lex_src = r#"[0-9]+ 'INT'
\+ '+'
\* '*'
"#;
        let grammar_src = "
%grmtools{YaccKind: Original(NoAction)}
%start Expr
%%
Expr : Expr '+' Term | Term;
Term : Term '*' Factor | Factor;
Factor : 'INT';";
        let input_src = "2*3+4";
        let grm = str::parse::<YaccGrammar<u16>>(grammar_src).unwrap();
        let (_, stable) = lrtable::from_yacc(&grm, lrtable::Minimiser::Pager).unwrap();
        let rt_parser = RTParserBuilder::new(&grm, &stable);
        let rule_ids = grm
            .tokens_map()
            .iter()
            .map(|(&n, &i)| (n.to_owned(), u32::from(i).to_u16().unwrap()))
            .collect();
        let lexer_rules = small_lexer(lex_src, rule_ids);
        let lexemes = small_lex(lexer_rules, input_src);
        let lexer = SmallLexer {
            lexemes,
            s: input_src,
        };

        let (parse_map, errs) = rt_parser.parse_map(
            &lexer,
            &|lexeme: TestLexeme| {
                let tidx = TIdx(lexeme.tok_id());
                let tn = &grm.token_name(tidx).unwrap();
                let lt = &input_src[lexeme.span().start()..lexeme.span().end()];
                TestParseMap::Term(tn, lt)
            },
            &|ridx, nodes| {
                let rule_name = &grm.rule_name_str(ridx);
                TestParseMap::NonTerm(rule_name, nodes)
            },
        );
        assert!(parse_map.is_some() && errs.is_empty());
        // Sanity check the `parse_generictree` output.
        check_parse_output(
            lex_src,
            grammar_src,
            input_src,
            "Expr
 Expr
  Term
   Term
    Factor
     INT 2
   * *
   Factor
    INT 3
 + +
 Term
  Factor
   INT 4
",
        );

        let expected_parse_map = {
            use TestParseMap::*;
            NonTerm(
                "Expr",
                vec![
                    NonTerm(
                        "Expr",
                        vec![NonTerm(
                            "Term",
                            vec![
                                NonTerm("Term", vec![NonTerm("Factor", vec![Term("INT", "2")])]),
                                Term("*", "*"),
                                NonTerm("Factor", vec![Term("INT", "3")]),
                            ],
                        )],
                    ),
                    Term("+", "+"),
                    NonTerm("Term", vec![NonTerm("Factor", vec![Term("INT", "4")])]),
                ],
            )
        };
        assert_eq!(parse_map, Some(expected_parse_map));
    }
}
