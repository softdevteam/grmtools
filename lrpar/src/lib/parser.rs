use std::{
    error::Error,
    fmt::{self, Debug, Display},
    hash::Hash,
    marker::PhantomData,
    time::{Duration, Instant},
    vec
};

use cactus::Cactus;
use cfgrammar::{yacc::YaccGrammar, RIdx, TIdx};
use lrtable::{Action, StIdx, StIdxStorageT, StateGraph, StateTable};
use num_traits::{AsPrimitive, PrimInt, Unsigned, Zero};

use crate::{
    cpctplus,
    lex::{LexError, Lexeme, Lexer},
    mf, panic, Span
};

#[cfg(test)]
const RECOVERY_TIME_BUDGET: u64 = 60_000; // milliseconds
#[cfg(not(test))]
const RECOVERY_TIME_BUDGET: u64 = 500; // milliseconds

/// A generic parse tree.
#[derive(Debug, Clone, PartialEq)]
pub enum Node<StorageT> {
    /// Terminals store a single lexeme.
    Term { lexeme: Lexeme<StorageT> },
    /// Nonterminals reference a rule and have zero or more `Node`s as children.
    Nonterm {
        ridx: RIdx<StorageT>,
        nodes: Vec<Node<StorageT>>
    }
}

impl<StorageT: 'static + PrimInt + Unsigned> Node<StorageT>
where
    usize: AsPrimitive<StorageT>
{
    /// Return a pretty-printed version of this node.
    pub fn pp(&self, grm: &YaccGrammar<StorageT>, input: &str) -> String {
        let mut st = vec![(0, self)]; // Stack of (indent level, node) pairs
        let mut s = String::new();
        while !st.is_empty() {
            let (indent, e) = st.pop().unwrap();
            for _ in 0..indent {
                s.push_str(" ");
            }
            match *e {
                Node::Term { lexeme } => {
                    let tidx = TIdx(lexeme.tok_id());
                    let tn = grm.token_name(tidx).unwrap();
                    let lt = &input[lexeme.span().start()..lexeme.span().end()];
                    s.push_str(&format!("{} {}\n", tn, lt));
                }
                Node::Nonterm { ridx, ref nodes } => {
                    s.push_str(&format!("{}\n", grm.rule_name(ridx)));
                    for x in nodes.iter().rev() {
                        st.push((indent + 1, x));
                    }
                }
            }
        }
        s
    }
}

pub(crate) type PStack = Vec<StIdx>; // Parse stack
pub(crate) type TokenCostFn<'a, StorageT> = &'a (dyn Fn(TIdx<StorageT>) -> u8 + 'a);
pub(crate) type ActionFn<'a, 'b, 'input, StorageT, ActionT> = &'a dyn Fn(
    RIdx<StorageT>,
    &'b dyn Lexer<'input, StorageT>,
    Span,
    vec::Drain<AStackType<ActionT, StorageT>>
) -> ActionT;

#[derive(Debug)]
pub enum AStackType<ActionT, StorageT> {
    ActionType(ActionT),
    Lexeme(Lexeme<StorageT>)
}

pub struct Parser<'a, 'b: 'a, 'input: 'b, StorageT: 'static + Eq + Hash, ActionT: 'a> {
    pub(crate) rcvry_kind: RecoveryKind,
    pub(crate) grm: &'a YaccGrammar<StorageT>,
    pub(crate) token_cost: Box<TokenCostFn<'a, StorageT>>,
    pub(crate) sgraph: &'a StateGraph<StorageT>,
    pub(crate) stable: &'a StateTable<StorageT>,
    pub(crate) lexer: &'b dyn Lexer<'input, StorageT>,
    // In the long term, we should remove the `lexemes` field entirely, as the `Lexer` API is
    // powerful enough to allow us to incrementally obtain lexemes and buffer them when necessary.
    pub(crate) lexemes: Vec<Lexeme<StorageT>>,
    actions: &'a [ActionFn<'a, 'b, 'input, StorageT, ActionT>]
}

impl<'a, 'b: 'a, 'input: 'b, StorageT: 'static + Debug + Hash + PrimInt + Unsigned>
    Parser<'a, 'b, 'input, StorageT, Node<StorageT>>
where
    usize: AsPrimitive<StorageT>,
    u32: AsPrimitive<StorageT>
{
    fn parse_generictree(
        rcvry_kind: RecoveryKind,
        grm: &YaccGrammar<StorageT>,
        token_cost: TokenCostFn<'a, StorageT>,
        sgraph: &StateGraph<StorageT>,
        stable: &StateTable<StorageT>,
        lexer: &'b dyn Lexer<'input, StorageT>,
        lexemes: Vec<Lexeme<StorageT>>
    ) -> (Option<Node<StorageT>>, Vec<LexParseError<StorageT>>) {
        for tidx in grm.iter_tidxs() {
            assert!(token_cost(tidx) > 0);
        }
        let mut actions: Vec<ActionFn<'a, 'b, 'input, StorageT, Node<StorageT>>> = Vec::new();
        actions.resize(usize::from(grm.prods_len()), &Parser::generic_ptree);
        let psr = Parser {
            rcvry_kind,
            grm,
            token_cost: Box::new(token_cost),
            sgraph,
            stable,
            lexer,
            lexemes,
            actions: actions.as_slice()
        };
        let mut pstack = vec![StIdx::from(StIdxStorageT::zero())];
        let mut astack = Vec::new();
        let mut errors = Vec::new();
        let mut spans = Vec::new();
        let accpt = psr.lr(0, &mut pstack, &mut astack, &mut errors, &mut spans);
        (accpt, errors)
    }

    fn generic_ptree(
        ridx: RIdx<StorageT>,
        _lexer: &dyn Lexer<StorageT>,
        _span: Span,
        astack: vec::Drain<AStackType<Node<StorageT>, StorageT>>
    ) -> Node<StorageT> {
        let mut nodes = Vec::with_capacity(astack.len());
        for a in astack {
            nodes.push(match a {
                AStackType::ActionType(n) => n,
                AStackType::Lexeme(lexeme) => Node::Term { lexeme }
            });
        }
        Node::Nonterm { ridx, nodes }
    }
}

impl<'a, 'b: 'a, 'input: 'b, StorageT: 'static + Debug + Hash + PrimInt + Unsigned>
    Parser<'a, 'b, 'input, StorageT, ()>
where
    usize: AsPrimitive<StorageT>,
    u32: AsPrimitive<StorageT>
{
    fn parse_noaction(
        rcvry_kind: RecoveryKind,
        grm: &YaccGrammar<StorageT>,
        token_cost: TokenCostFn<'a, StorageT>,
        sgraph: &StateGraph<StorageT>,
        stable: &StateTable<StorageT>,
        lexer: &'b dyn Lexer<'input, StorageT>,
        lexemes: Vec<Lexeme<StorageT>>
    ) -> Vec<LexParseError<StorageT>> {
        for tidx in grm.iter_tidxs() {
            assert!(token_cost(tidx) > 0);
        }
        let mut actions: Vec<ActionFn<'a, 'b, 'input, StorageT, ()>> = Vec::new();
        actions.resize(usize::from(grm.prods_len()), &Parser::noaction);
        let psr = Parser {
            rcvry_kind,
            grm,
            token_cost: Box::new(token_cost),
            sgraph,
            stable,
            lexer,
            lexemes,
            actions: actions.as_slice()
        };
        let mut pstack = vec![StIdx::from(StIdxStorageT::zero())];
        let mut astack = Vec::new();
        let mut errors = Vec::new();
        let mut spans = Vec::new();
        psr.lr(0, &mut pstack, &mut astack, &mut errors, &mut spans);
        errors
    }

    fn noaction(
        _ridx: RIdx<StorageT>,
        _lexer: &dyn Lexer<StorageT>,
        _span: Span,
        _astack: vec::Drain<AStackType<(), StorageT>>
    ) {
    }
}

impl<
        'a,
        'b: 'a,
        'input: 'b,
        StorageT: 'static + Debug + Hash + PrimInt + Unsigned,
        ActionT: 'a
    > Parser<'a, 'b, 'input, StorageT, ActionT>
where
    usize: AsPrimitive<StorageT>,
    u32: AsPrimitive<StorageT>
{
    fn parse_actions(
        rcvry_kind: RecoveryKind,
        grm: &'a YaccGrammar<StorageT>,
        token_cost: TokenCostFn<'a, StorageT>,
        sgraph: &'a StateGraph<StorageT>,
        stable: &'a StateTable<StorageT>,
        lexer: &'b dyn Lexer<'input, StorageT>,
        lexemes: Vec<Lexeme<StorageT>>,
        actions: &'a [ActionFn<'a, 'b, 'input, StorageT, ActionT>]
    ) -> (Option<ActionT>, Vec<LexParseError<StorageT>>) {
        for tidx in grm.iter_tidxs() {
            assert!(token_cost(tidx) > 0);
        }
        let psr = Parser {
            rcvry_kind,
            grm,
            token_cost: Box::new(token_cost),
            sgraph,
            stable,
            lexer,
            lexemes,
            actions
        };
        let mut pstack = vec![StIdx::from(StIdxStorageT::zero())];
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
    pub fn lr(
        &self,
        mut laidx: usize,
        pstack: &mut PStack,
        astack: &mut Vec<AStackType<ActionT, StorageT>>,
        errors: &mut Vec<LexParseError<StorageT>>,
        spans: &mut Vec<Span>
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
                        astack.drain(pop_idx - 1..)
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
                    match astack.drain(..).nth(0).unwrap() {
                        AStackType::ActionType(v) => return Some(v),
                        _ => unreachable!()
                    }
                }
                Action::Error => {
                    if recoverer.is_none() {
                        recoverer = Some(match self.rcvry_kind {
                            RecoveryKind::CPCTPlus => cpctplus::recoverer(self),
                            RecoveryKind::MF => mf::recoverer(self),
                            RecoveryKind::Panic => panic::recoverer(self),
                            RecoveryKind::None => {
                                let la_lexeme = self.next_lexeme(laidx);
                                errors.push(
                                    ParseError {
                                        stidx,
                                        lexeme: la_lexeme,
                                        repairs: vec![]
                                    }
                                    .into()
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
                            repairs
                        }
                        .into()
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
    pub fn lr_upto(
        &self,
        lexeme_prefix: Option<Lexeme<StorageT>>,
        mut laidx: usize,
        end_laidx: usize,
        pstack: &mut PStack,
        astack: &mut Option<&mut Vec<AStackType<ActionT, StorageT>>>,
        spans: &mut Option<&mut Vec<Span>>
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
                                    spans_uw[spans_uw.len() - 1].end()
                                )
                            } else {
                                Span::new(
                                    spans_uw[spans_uw.len() - 1].start(),
                                    spans_uw[spans_uw.len() - 1].end()
                                )
                            };
                            spans_uw.truncate(pop_idx - 1);
                            spans_uw.push(span);

                            let v = AStackType::ActionType(self.actions[usize::from(pidx)](
                                ridx,
                                self.lexer,
                                span,
                                astack_uw.drain(pop_idx - 1..)
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
                        if let Some(ref mut spans_uw) = spans {
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
    pub(crate) fn next_lexeme(&self, laidx: usize) -> Lexeme<StorageT> {
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

            Lexeme::new(
                StorageT::from(u32::from(self.grm.eof_token_idx())).unwrap(),
                last_la_end,
                None
            )
        }
    }

    /// Return the `TIdx` of the next lexeme (if `laidx` == `self.lexemes.len()` this will be the
    /// EOF `TIdx`).
    pub(crate) fn next_tidx(&self, laidx: usize) -> TIdx<StorageT> {
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
    pub(crate) fn lr_cactus(
        &self,
        lexeme_prefix: Option<Lexeme<StorageT>>,
        mut laidx: usize,
        end_laidx: usize,
        mut pstack: Cactus<StIdx>,
        tstack: &mut Option<&mut Vec<Node<StorageT>>>
    ) -> (usize, Cactus<StIdx>) {
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
                            .collect::<Vec<Node<StorageT>>>();
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
                        debug_assert_eq!((&tstack_uw).len(), 1);
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

pub trait Recoverer<StorageT: Hash + PrimInt + Unsigned, ActionT> {
    fn recover(
        &self,
        finish_by: Instant,
        parser: &Parser<StorageT, ActionT>,
        in_laidx: usize,
        in_pstack: &mut PStack,
        astack: &mut Vec<AStackType<ActionT, StorageT>>,
        spans: &mut Vec<Span>
    ) -> (usize, Vec<Vec<ParseRepair<StorageT>>>);
}

/// What recovery algorithm should be used when a syntax error is encountered?
#[derive(Clone, Copy, Debug)]
pub enum RecoveryKind {
    /// The CPCT+ algorithm from Diekmann/Tratt "Don't Panic! Better, Fewer, Syntax Errors for LR
    /// Parsers".
    CPCTPlus,
    /// The MF algorithm from Diekmann/Tratt "Don't Panic! Better, Fewer, Syntax Errors for LR
    /// Parsers".
    #[doc(hidden)]
    MF,
    #[doc(hidden)]
    Panic,
    /// Don't use error recovery: return as soon as the first syntax error is encountered.
    None
}

/// A lexing or parsing error. Although the two are quite distinct in terms of what can be reported
/// to users, both can (at least conceptually) occur at any point of the intertwined lexing/parsing
/// process.
#[derive(Debug)]
pub enum LexParseError<StorageT: Hash> {
    LexError(LexError),
    ParseError(ParseError<StorageT>)
}

impl<StorageT: Hash + PrimInt + Unsigned> LexParseError<StorageT> {
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
        lexer: &dyn Lexer<StorageT>,
        epp: &dyn Fn(TIdx<StorageT>) -> Option<&'a str>
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
                        out.push_str(&format!("\n  {}{}: ", " ".repeat(padding), i + 1));
                        let mut rs_out = Vec::new();
                        for r in rs {
                            match r {
                                ParseRepair::Insert(tidx) => {
                                    rs_out.push(format!("Insert {}", epp(*tidx).unwrap()));
                                }
                                ParseRepair::Shift(l) | ParseRepair::Delete(l) => {
                                    let t = &lexer.span_str(l.span()).replace("\n", "\\n");
                                    if let ParseRepair::Delete(_) = *r {
                                        rs_out.push(format!("Delete {}", t));
                                    } else {
                                        rs_out.push(format!("Shift {}", t));
                                    }
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

impl<StorageT: Debug + Hash> fmt::Display for LexParseError<StorageT> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            LexParseError::LexError(ref e) => Display::fmt(e, f),
            LexParseError::ParseError(ref e) => Display::fmt(e, f)
        }
    }
}

impl<StorageT: Debug + Hash> Error for LexParseError<StorageT> {}

impl<StorageT: Hash> From<LexError> for LexParseError<StorageT> {
    fn from(err: LexError) -> LexParseError<StorageT> {
        LexParseError::LexError(err)
    }
}

impl<StorageT: Hash> From<ParseError<StorageT>> for LexParseError<StorageT> {
    fn from(err: ParseError<StorageT>) -> LexParseError<StorageT> {
        LexParseError::ParseError(err)
    }
}

/// A run-time parser builder.
pub struct RTParserBuilder<'a, StorageT: Eq + Hash> {
    grm: &'a YaccGrammar<StorageT>,
    sgraph: &'a StateGraph<StorageT>,
    stable: &'a StateTable<StorageT>,
    recoverer: RecoveryKind,
    term_costs: &'a dyn Fn(TIdx<StorageT>) -> u8,
    phantom: PhantomData<StorageT>
}

impl<'a, StorageT: 'static + Debug + Hash + PrimInt + Unsigned> RTParserBuilder<'a, StorageT>
where
    usize: AsPrimitive<StorageT>,
    u32: AsPrimitive<StorageT>
{
    /// Create a new run-time parser from a `YaccGrammar`, a `StateGraph`, and a `StateTable`.
    pub fn new(
        grm: &'a YaccGrammar<StorageT>,
        sgraph: &'a StateGraph<StorageT>,
        stable: &'a StateTable<StorageT>
    ) -> Self {
        RTParserBuilder {
            grm,
            sgraph,
            stable,
            recoverer: RecoveryKind::CPCTPlus,
            term_costs: &|_| 1,
            phantom: PhantomData
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

    /// Parse input, and (if possible) return a generic parse tree. See the arguments for
    /// [`parse_actions`](#method.parse_actions) for more details about the return value.
    pub fn parse_generictree(
        &self,
        lexer: &dyn Lexer<StorageT>
    ) -> (Option<Node<StorageT>>, Vec<LexParseError<StorageT>>) {
        let mut lexemes = vec![];
        for e in lexer.iter().collect::<Vec<_>>() {
            match e {
                Ok(l) => lexemes.push(l),
                Err(e) => return (None, vec![e.into()])
            }
        }
        Parser::<StorageT, Node<StorageT>>::parse_generictree(
            self.recoverer,
            self.grm,
            self.term_costs,
            self.sgraph,
            self.stable,
            lexer,
            lexemes
        )
    }

    /// Parse input, returning any errors found. See the arguments for
    /// [`parse_actions`](#method.parse_actions) for more details about the return value.
    pub fn parse_noaction(&self, lexer: &dyn Lexer<StorageT>) -> Vec<LexParseError<StorageT>> {
        let mut lexemes = vec![];
        for e in lexer.iter().collect::<Vec<_>>() {
            match e {
                Ok(l) => lexemes.push(l),
                Err(e) => return vec![e.into()]
            }
        }
        Parser::<StorageT, ()>::parse_noaction(
            self.recoverer,
            self.grm,
            self.term_costs,
            self.sgraph,
            self.stable,
            lexer,
            lexemes
        )
    }

    /// Parse input, execute actions, and return the associated value (if possible) and/or any
    /// lexing/parsing errors encountered. Note that the two parts of the (value, errors) return
    /// pair are entirely independent: one can encounter errors without a value being produced
    /// (`None, [...]`), errors and a value (`Some(...), [...]`), as well as a value and no errors
    /// (`Some(...), []`). Errors are sorted by the position they were found in the input and can
    /// be a mix of lexing and parsing errors.
    pub fn parse_actions<'b: 'a, 'input: 'b, ActionT: 'a>(
        &self,
        lexer: &'b dyn Lexer<'input, StorageT>,
        actions: &'a [ActionFn<'a, 'b, 'input, StorageT, ActionT>]
    ) -> (Option<ActionT>, Vec<LexParseError<StorageT>>) {
        let mut lexemes = vec![];
        for e in lexer.iter().collect::<Vec<_>>() {
            match e {
                Ok(l) => lexemes.push(l),
                Err(e) => return (None, vec![e.into()])
            }
        }
        Parser::parse_actions(
            self.recoverer,
            self.grm,
            self.term_costs,
            self.sgraph,
            self.stable,
            lexer,
            lexemes,
            actions
        )
    }
}

/// After a parse error is encountered, the parser attempts to find a way of recovering. Each entry
/// in the sequence of repairs is represented by a `ParseRepair`.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum ParseRepair<StorageT: Hash> {
    /// Insert a `Symbol::Token`.
    Insert(TIdx<StorageT>),
    /// Delete a symbol.
    Delete(Lexeme<StorageT>),
    /// Shift a symbol.
    Shift(Lexeme<StorageT>)
}

/// Records a single parse error.
#[derive(Clone, Debug, PartialEq)]
pub struct ParseError<StorageT: Hash> {
    stidx: StIdx,
    lexeme: Lexeme<StorageT>,
    repairs: Vec<Vec<ParseRepair<StorageT>>>
}

impl<StorageT: Debug + Hash> Display for ParseError<StorageT> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Parse error at lexeme {:?}", self.lexeme)
    }
}

impl<StorageT: Debug + Hash> Error for ParseError<StorageT> {}

impl<StorageT: Hash + PrimInt + Unsigned> ParseError<StorageT> {
    /// Return the state table index where this error was detected.
    pub fn stidx(&self) -> StIdx {
        self.stidx
    }

    /// Return the lexeme where this error was detected.
    pub fn lexeme(&self) -> &Lexeme<StorageT> {
        &self.lexeme
    }

    /// Return the repairs found that would fix this error. Note that there are infinite number of
    /// possible repairs for any error, so this is by definition a (finite) subset.
    pub fn repairs(&self) -> &Vec<Vec<ParseRepair<StorageT>>> {
        &self.repairs
    }
}

#[cfg(test)]
pub(crate) mod test {
    use std::collections::HashMap;

    use cfgrammar::yacc::{YaccGrammar, YaccKind, YaccOriginalActionKind};
    use lrtable::{from_yacc, Minimiser};
    use num_traits::ToPrimitive;
    use regex::Regex;

    use super::*;
    use crate::{lex::Lexeme, Span};

    pub(crate) fn do_parse(
        rcvry_kind: RecoveryKind,
        lexs: &str,
        grms: &str,
        input: &str
    ) -> (
        YaccGrammar<u16>,
        Result<Node<u16>, (Option<Node<u16>>, Vec<LexParseError<u16>>)>
    ) {
        do_parse_with_costs(rcvry_kind, lexs, grms, input, &HashMap::new())
    }

    pub(crate) fn do_parse_with_costs(
        rcvry_kind: RecoveryKind,
        lexs: &str,
        grms: &str,
        input: &str,
        costs: &HashMap<&str, u8>
    ) -> (
        YaccGrammar<u16>,
        Result<Node<u16>, (Option<Node<u16>>, Vec<LexParseError<u16>>)>
    ) {
        let grm = YaccGrammar::<u16>::new_with_storaget(
            YaccKind::Original(YaccOriginalActionKind::GenericParseTree),
            grms
        )
        .unwrap();
        let (sgraph, stable) = from_yacc(&grm, Minimiser::Pager).unwrap();
        let rule_ids = grm
            .tokens_map()
            .iter()
            .map(|(&n, &i)| (n.to_owned(), u32::from(i).to_u16().unwrap()))
            .collect();
        let lexer_rules = small_lexer(lexs, rule_ids);
        let lexemes = small_lex(lexer_rules, input);
        let lexer = SmallLexer { lexemes };
        let costs_tidx = costs
            .iter()
            .map(|(k, v)| (grm.token_idx(k).unwrap(), v))
            .collect::<HashMap<_, _>>();
        let (r, errs) = RTParserBuilder::new(&grm, &sgraph, &stable)
            .recoverer(rcvry_kind)
            .term_costs(&|tidx| **costs_tidx.get(&tidx).unwrap_or(&&1))
            .parse_generictree(&lexer);
        if r.is_some() && errs.is_empty() {
            (grm, Ok(r.unwrap()))
        } else if r.is_some() && !errs.is_empty() {
            (grm, Err((Some(r.unwrap()), errs)))
        } else {
            (grm, Err((None, errs)))
        }
    }

    fn check_parse_output(lexs: &str, grms: &str, input: &str, expected: &str) {
        let (grm, pt) = do_parse(RecoveryKind::CPCTPlus, lexs, grms, input);
        assert_eq!(expected, pt.unwrap().pp(&grm, &input));
    }

    // SmallLexer is our highly simplified version of lrlex (allowing us to avoid having to have
    // lrlex as a dependency of lrpar). The format is the same as lrlex *except*:
    //   * The initial "%%" isn't needed, and only "'" is valid as a rule name delimiter.
    //   * "Unnamed" rules aren't allowed (e.g. you can't have a rule which discards whitespaces).
    struct SmallLexer<StorageT> {
        lexemes: Vec<Lexeme<StorageT>>
    }

    impl<'input, StorageT: Hash + PrimInt + Unsigned> Lexer<'input, StorageT> for SmallLexer<StorageT> {
        fn iter<'a>(&'a self) -> Box<dyn Iterator<Item = Result<Lexeme<StorageT>, LexError>> + 'a> {
            Box::new(self.lexemes.iter().map(|x| Ok(*x)))
        }

        fn span_str(&self, _: Span) -> &'input str {
            unreachable!();
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
        for l in lexs.split("\n").map(|x| x.trim()).filter(|x| !x.is_empty()) {
            assert!(l.rfind('\'') == Some(l.len() - 1));
            let i = l[..l.len() - 1].rfind('\'').unwrap();
            let name = &l[i + 1..l.len() - 1];
            let re = &l[..i - 1].trim();
            rules.push((
                ids_map[name],
                Regex::new(&format!("\\A(?:{})", re)).unwrap()
            ));
        }
        rules
    }

    fn small_lex(rules: Vec<(u16, Regex)>, input: &str) -> Vec<Lexeme<u16>> {
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
            lexemes.push(Lexeme::new(longest_tok_id, i, Some(longest)));
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
"
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
            &lexs, &grms, "", "S
 L
"
        );

        check_parse_output(
            &lexs,
            &grms,
            "x",
            "S
 L
  ID x
"
        );
    }

    #[test]
    fn recursive_parse() {
        let lexs = "\\+ '+'
                    \\* '*'
                    [0-9]+ 'INT'";
        let grms = "%start Expr
%%
Expr : Term '+' Expr | Term;
Term : Factor '*' Term | Factor;
Factor : 'INT';";

        check_parse_output(
            &lexs,
            &grms,
            "2+3*4",
            "Expr
 Term
  Factor
   INT 2
 + +
 Expr
  Term
   Factor
    INT 3
   * *
   Term
    Factor
     INT 4
"
        );
        check_parse_output(
            &lexs,
            &grms,
            "2*3+4",
            "Expr
 Term
  Factor
   INT 2
  * *
  Term
   Factor
    INT 3
 + +
 Expr
  Term
   Factor
    INT 4
"
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
            &lexs,
            &grms,
            "f()",
            "Call
 ID f
 ( (
 ) )
"
        );

        let (grm, pr) = do_parse(RecoveryKind::MF, &lexs, &grms, "f(");
        let (_, errs) = pr.unwrap_err();
        assert_eq!(errs.len(), 1);
        let err_tok_id = usize::from(grm.eof_token_idx()).to_u16().unwrap();
        match &errs[0] {
            LexParseError::ParseError(e) => {
                assert_eq!(e.lexeme(), &Lexeme::new(err_tok_id, 2, None));
                assert!(e.lexeme().inserted());
            }
            _ => unreachable!()
        }

        let (grm, pr) = do_parse(RecoveryKind::MF, &lexs, &grms, "f(f(");
        let (_, errs) = pr.unwrap_err();
        assert_eq!(errs.len(), 1);
        let err_tok_id = usize::from(grm.token_idx("ID").unwrap()).to_u16().unwrap();
        match &errs[0] {
            LexParseError::ParseError(e) => {
                assert_eq!(e.lexeme(), &Lexeme::new(err_tok_id, 2, Some(1)));
                assert!(!e.lexeme().inserted());
            }
            _ => unreachable!()
        }
    }
}
