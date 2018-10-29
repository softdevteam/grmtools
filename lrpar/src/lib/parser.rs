// Copyright (c) 2017 King's College London
// created by the Software Development Team <http://soft-dev.org/>
//
// The Universal Permissive License (UPL), Version 1.0
//
// Subject to the condition set forth below, permission is hereby granted to any person obtaining a
// copy of this software, associated documentation and/or data (collectively the "Software"), free
// of charge and under any and all copyright rights in the Software, and any and all patent rights
// owned or freely licensable by each licensor hereunder covering either (i) the unmodified
// Software as contributed to or provided by such licensor, or (ii) the Larger Works (as defined
// below), to deal in both
//
// (a) the Software, and
// (b) any piece of software and/or hardware listed in the lrgrwrks.txt file
// if one is included with the Software (each a "Larger Work" to which the Software is contributed
// by such licensors),
//
// without restriction, including without limitation the rights to copy, create derivative works
// of, display, perform, and distribute the Software and make, use, sell, offer for sale, import,
// export, have made, and have sold the Software and the Larger Work(s), and to sublicense the
// foregoing rights on either these or other terms.
//
// This license is subject to the following condition: The above copyright notice and either this
// complete permission notice or at a minimum a reference to the UPL must be included in all copies
// or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING
// BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
// NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
// DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

use std::{
    error::Error,
    fmt::{self, Debug, Display},
    hash::Hash,
    marker::PhantomData,
    time::{Duration, Instant}
};

use cactus::Cactus;
use cfgrammar::{yacc::YaccGrammar, RIdx, TIdx};
use lrtable::{Action, StIdx, StIdxStorageT, StateGraph, StateTable};
use num_traits::{AsPrimitive, PrimInt, Unsigned, Zero};

use cpctplus;
use lex::{LexError, Lexeme, Lexer};
use mf;
use panic;

const RECOVERY_TIME_BUDGET: u64 = 500; // milliseconds

#[derive(Debug, Clone, PartialEq)]
pub enum Node<StorageT> {
    Term {
        lexeme: Lexeme<StorageT>
    },
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
                    let lt = &input[lexeme.start()..lexeme.start() + lexeme.len()];
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
pub(crate) type TStack<StorageT> = Vec<Node<StorageT>>; // Parse tree stack

pub struct Parser<'a, StorageT: 'a + Eq + Hash> {
    pub rcvry_kind: RecoveryKind,
    pub grm: &'a YaccGrammar<StorageT>,
    pub token_cost: &'a Fn(TIdx<StorageT>) -> u8,
    pub sgraph: &'a StateGraph<StorageT>,
    pub stable: &'a StateTable<StorageT>,
    pub lexemes: &'a [Lexeme<StorageT>]
}

impl<'a, StorageT: 'static + Debug + Hash + PrimInt + Unsigned> Parser<'a, StorageT>
where
    usize: AsPrimitive<StorageT>,
    u32: AsPrimitive<StorageT>
{
    fn parse<F>(
        rcvry_kind: RecoveryKind,
        grm: &YaccGrammar<StorageT>,
        token_cost: F,
        sgraph: &StateGraph<StorageT>,
        stable: &StateTable<StorageT>,
        lexemes: &[Lexeme<StorageT>]
    ) -> Result<Node<StorageT>, (Option<Node<StorageT>>, Vec<ParseError<StorageT>>)>
    where
        F: Fn(TIdx<StorageT>) -> u8
    {
        for tidx in grm.iter_tidxs() {
            assert!(token_cost(tidx) > 0);
        }
        let psr = Parser {
            rcvry_kind,
            grm,
            token_cost: &token_cost,
            sgraph,
            stable,
            lexemes
        };
        let mut pstack = vec![StIdx::from(StIdxStorageT::zero())];
        let mut tstack: Vec<Node<StorageT>> = Vec::new();
        let mut errors: Vec<ParseError<StorageT>> = Vec::new();
        let accpt = psr.lr(0, &mut pstack, &mut tstack, &mut errors);
        match (accpt, errors.is_empty()) {
            (true, true) => Ok(tstack.drain(..).nth(0).unwrap()),
            (true, false) => Err((Some(tstack.drain(..).nth(0).unwrap()), errors)),
            (false, false) => Err((None, errors)),
            (false, true) => panic!("Internal error")
        }
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
    /// Return `true` if the parse reached an accept state (i.e. all the input was consumed,
    /// possibly after making repairs) or `false` (i.e. some of the input was not consumed, even
    /// after possibly making repairs) otherwise.
    pub fn lr(
        &self,
        mut laidx: usize,
        pstack: &mut PStack,
        tstack: &mut TStack<StorageT>,
        errors: &mut Vec<ParseError<StorageT>>
    ) -> bool {
        let mut recoverer = None;
        let mut recovery_budget = Duration::from_millis(RECOVERY_TIME_BUDGET);
        loop {
            let stidx = *pstack.last().unwrap();
            let la_tidx = self.next_tidx(laidx);

            match self.stable.action(stidx, la_tidx) {
                Action::Reduce(pidx) => {
                    let ridx = self.grm.prod_to_rule(pidx);
                    let pop_idx = pstack.len() - self.grm.prod(pidx).len();
                    let nodes = tstack.drain(pop_idx - 1..).collect::<Vec<Node<StorageT>>>();
                    tstack.push(Node::Nonterm { ridx, nodes });

                    pstack.drain(pop_idx..);
                    let prior = *pstack.last().unwrap();
                    pstack.push(self.stable.goto(prior, ridx).unwrap());
                }
                Action::Shift(state_id) => {
                    let la_lexeme = self.next_lexeme(laidx);
                    tstack.push(Node::Term { lexeme: la_lexeme });
                    pstack.push(state_id);
                    laidx += 1;
                }
                Action::Accept => {
                    debug_assert_eq!(la_tidx, self.grm.eof_token_idx());
                    debug_assert_eq!(tstack.len(), 1);
                    return true;
                }
                Action::Error => {
                    if recoverer.is_none() {
                        recoverer = Some(match self.rcvry_kind {
                            RecoveryKind::CPCTPlus => cpctplus::recoverer(self),
                            RecoveryKind::MF => mf::recoverer(self),
                            RecoveryKind::Panic => panic::recoverer(self),
                            RecoveryKind::None => {
                                let la_lexeme = self.next_lexeme(laidx);
                                errors.push(ParseError {
                                    stidx,
                                    lexeme: la_lexeme,
                                    repairs: vec![]
                                });
                                return false;
                            }
                        });
                    }

                    let before = Instant::now();
                    let finish_by = before + recovery_budget;
                    let (new_laidx, repairs) = recoverer
                        .as_ref()
                        .unwrap()
                        .as_ref()
                        .recover(finish_by, self, laidx, pstack, tstack);
                    let after = Instant::now();
                    recovery_budget = recovery_budget
                        .checked_sub(after - before)
                        .unwrap_or_else(|| Duration::new(0, 0));
                    let keep_going = !repairs.is_empty();
                    let la_lexeme = self.next_lexeme(laidx);
                    errors.push(ParseError {
                        stidx,
                        lexeme: la_lexeme,
                        repairs
                    });
                    if !keep_going {
                        return false;
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
        tstack: &mut Option<&mut Vec<Node<StorageT>>>
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
                    if let Some(ref mut tstack_uw) = *tstack {
                        let nodes = tstack_uw
                            .drain(pop_idx - 1..)
                            .collect::<Vec<Node<StorageT>>>();
                        tstack_uw.push(Node::Nonterm { ridx, nodes });
                    }

                    pstack.drain(pop_idx..);
                    let prior = *pstack.last().unwrap();
                    pstack.push(self.stable.goto(prior, ridx).unwrap());
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
                last_la.start() + last_la.len()
            };

            Lexeme::new(
                StorageT::from(u32::from(self.grm.eof_token_idx())).unwrap(),
                last_la_end,
                0
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
                    if let Some(ref mut tstack_uw) = *tstack {
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

pub trait Recoverer<StorageT: Hash + PrimInt + Unsigned> {
    fn recover(
        &self,
        Instant,
        &Parser<StorageT>,
        usize,
        &mut PStack,
        &mut TStack<StorageT>
    ) -> (usize, Vec<Vec<ParseRepair<StorageT>>>);
}

#[derive(Clone, Copy, Debug)]
pub enum RecoveryKind {
    CPCTPlus,
    MF,
    Panic,
    None
}

#[derive(Debug)]
pub enum LexParseError<StorageT> {
    LexError(LexError),
    ParseError(Option<Node<StorageT>>, Vec<ParseError<StorageT>>)
}

impl<StorageT: Debug> Error for LexParseError<StorageT> {}

impl<StorageT: Debug> fmt::Display for LexParseError<StorageT> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            LexParseError::LexError(ref e) => Display::fmt(e, f),
            LexParseError::ParseError(_, ref e) => e.fmt(f)
        }
    }
}

impl<StorageT> From<LexError> for LexParseError<StorageT> {
    fn from(err: LexError) -> LexParseError<StorageT> {
        LexParseError::LexError(err)
    }
}

impl<StorageT> From<(Option<Node<StorageT>>, Vec<ParseError<StorageT>>)>
    for LexParseError<StorageT>
{
    fn from(err: (Option<Node<StorageT>>, Vec<ParseError<StorageT>>)) -> LexParseError<StorageT> {
        LexParseError::ParseError(err.0, err.1)
    }
}

pub struct RTParserBuilder<'a, StorageT: Eq + Hash> {
    grm: &'a YaccGrammar<StorageT>,
    sgraph: &'a StateGraph<StorageT>,
    stable: &'a StateTable<StorageT>,
    recoverer: RecoveryKind,
    term_costs: &'a Fn(TIdx<StorageT>) -> u8,
    phantom: PhantomData<StorageT>
}

impl<'a, StorageT: 'static + Debug + Hash + PrimInt + Unsigned> RTParserBuilder<'a, StorageT>
where
    usize: AsPrimitive<StorageT>,
    u32: AsPrimitive<StorageT>
{
    pub fn new(
        grm: &'a YaccGrammar<StorageT>,
        sgraph: &'a StateGraph<StorageT>,
        stable: &'a StateTable<StorageT>
    ) -> Self {
        RTParserBuilder {
            grm,
            sgraph,
            stable,
            recoverer: RecoveryKind::MF,
            term_costs: &|_| 1,
            phantom: PhantomData
        }
    }

    /// Set the recoverer for this parser to `rk`.
    pub fn recoverer(mut self, rk: RecoveryKind) -> Self {
        self.recoverer = rk;
        self
    }

    pub fn term_costs(mut self, f: &'a Fn(TIdx<StorageT>) -> u8) -> Self {
        self.term_costs = f;
        self
    }

    /// Parse input. On success return a parse tree. On failure, return a `LexParseError`: a
    /// `LexError` means that no parse tree was produced; a `ParseError` may (if its first element
    /// is `Some(...)`) return a parse tree (with parts filled in by this builder's recoverer).
    pub fn parse(
        &self,
        lexer: &mut Lexer<StorageT>
    ) -> Result<Node<StorageT>, LexParseError<StorageT>> {
        Ok(Parser::parse(
            self.recoverer,
            self.grm,
            self.term_costs,
            self.sgraph,
            self.stable,
            &lexer.all_lexemes()?[..]
        )?)
    }
}

/// After a parse error is encountered, the parser attempts to find a way of recovering. Each entry
/// in the sequence of repairs is represented by a `ParseRepair`.
#[derive(Clone, Debug, PartialEq)]
pub enum ParseRepair<StorageT> {
    /// Insert a `Symbol::Token`.
    Insert(TIdx<StorageT>),
    /// Insert one of the sequences of `Symbol::Token`s.
    InsertSeq(Vec<Vec<TIdx<StorageT>>>),
    /// Delete a symbol.
    Delete(Lexeme<StorageT>),
    /// Shift a symbol.
    Shift(Lexeme<StorageT>)
}

/// Records a single parse error.
#[derive(Clone, Debug, PartialEq)]
pub struct ParseError<StorageT> {
    stidx: StIdx,
    lexeme: Lexeme<StorageT>,
    repairs: Vec<Vec<ParseRepair<StorageT>>>
}

impl<StorageT: Debug> Display for ParseError<StorageT> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Parse error at lexeme {:?}", self.lexeme)
    }
}

impl<StorageT: Debug> Error for ParseError<StorageT> {}

impl<StorageT: PrimInt + Unsigned> ParseError<StorageT> {
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

    use cfgrammar::yacc::{YaccGrammar, YaccKind};
    use lrtable::{from_yacc, Minimiser};
    use num_traits::ToPrimitive;
    use regex::Regex;

    use super::*;
    use lex::Lexeme;

    pub(crate) fn do_parse(
        rcvry_kind: RecoveryKind,
        lexs: &str,
        grms: &str,
        input: &str
    ) -> (
        YaccGrammar<u16>,
        Result<Node<u16>, (Option<Node<u16>>, Vec<ParseError<u16>>)>
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
        Result<Node<u16>, (Option<Node<u16>>, Vec<ParseError<u16>>)>
    ) {
        let grm = YaccGrammar::<u16>::new_with_storaget(YaccKind::Original, grms).unwrap();
        let (sgraph, stable) = from_yacc(&grm, Minimiser::Pager).unwrap();
        let rule_ids = grm
            .tokens_map()
            .iter()
            .map(|(&n, &i)| (n.to_owned(), u32::from(i).to_u16().unwrap()))
            .collect();
        let lexer_rules = small_lexer(lexs, rule_ids);
        let lexemes = small_lex(lexer_rules, input);
        let mut lexer = SmallLexer { lexemes, i: 0 };
        let costs_tidx = costs
            .iter()
            .map(|(k, v)| (grm.token_idx(k).unwrap(), v))
            .collect::<HashMap<_, _>>();
        let r = match RTParserBuilder::new(&grm, &sgraph, &stable)
            .recoverer(rcvry_kind)
            .term_costs(&|tidx| **costs_tidx.get(&tidx).unwrap_or(&&1))
            .parse(&mut lexer)
        {
            Ok(r) => Ok(r),
            Err(LexParseError::ParseError(r1, r2)) => Err((r1, r2)),
            _ => unreachable!()
        };
        (grm, r)
    }

    fn check_parse_output(lexs: &str, grms: &str, input: &str, expected: &str) {
        let (grm, pt) = do_parse(RecoveryKind::MF, lexs, grms, input);
        assert_eq!(expected, pt.unwrap().pp(&grm, &input));
    }

    // SmallLexer is our highly simplified version of lrlex (allowing us to avoid having to have
    // lrlex as a dependency of lrpar). The format is the same as lrlex *except*:
    //   * The initial "%%" isn't needed, and only "'" is valid as a rule name delimiter.
    //   * "Unnamed" rules aren't allowed (e.g. you can't have a rule which discards whitespaces).
    struct SmallLexer<StorageT> {
        lexemes: Vec<Lexeme<StorageT>>,
        i: usize
    }

    impl<StorageT: Hash + PrimInt + Unsigned> Lexer<StorageT> for SmallLexer<StorageT> {
        fn next(&mut self) -> Option<Result<Lexeme<StorageT>, LexError>> {
            let old_i = self.i;
            if old_i < self.lexemes.len() {
                self.i = old_i + 1;
                return Some(Ok(self.lexemes[old_i]));
            }
            None
        }

        fn line_and_col(&self, _: &Lexeme<StorageT>) -> Result<(usize, usize), ()> {
            unreachable!();
        }
    }

    fn small_lexer(lexs: &str, ids_map: HashMap<String, u16>) -> Vec<(u16, Regex)> {
        let mut rules = Vec::new();
        for l in lexs.split("\n").map(|x| x.trim()).filter(|x| !x.is_empty()) {
            assert!(l.rfind("'") == Some(l.len() - 1));
            let i = l[..l.len() - 1].rfind("'").unwrap();
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
",
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
        assert_eq!(errs[0].lexeme(), &Lexeme::new(err_tok_id, 2, 0));

        let (grm, pr) = do_parse(RecoveryKind::MF, &lexs, &grms, "f(f(");
        let (_, errs) = pr.unwrap_err();
        assert_eq!(errs.len(), 1);
        let err_tok_id = usize::from(grm.token_idx("ID").unwrap()).to_u16().unwrap();
        assert_eq!(errs[0].lexeme(), &Lexeme::new(err_tok_id, 2, 1));
    }
}
