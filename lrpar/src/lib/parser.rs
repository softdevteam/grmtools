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

use std::fmt::{self, Debug, Display};
use std::error::Error;
use std::hash::Hash;
use std::time::{Duration, Instant};

use cactus::Cactus;
use cfgrammar::{Grammar, RIdx, TIdx};
use cfgrammar::yacc::YaccGrammar;
use lrlex::Lexeme;
use lrtable::{Action, StateGraph, StateTable, StIdx};
use num_traits::{AsPrimitive, PrimInt, Unsigned};

use mf;
use cpctplus;
use panic;

const RECOVERY_TIME_BUDGET: u64 = 500; // milliseconds

#[derive(Debug, Clone, PartialEq)]
pub enum Node<StorageT> {
    Term{lexeme: Lexeme<StorageT>},
    Nonterm{rule_idx: RIdx<StorageT>, nodes: Vec<Node<StorageT>>}
}

impl<StorageT: 'static + PrimInt + Unsigned> Node<StorageT>
where usize: AsPrimitive<StorageT>
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
                Node::Term{lexeme} => {
                    let t_idx = TIdx(lexeme.tok_id());
                    let tn = grm.token_name(t_idx).unwrap();
                    let lt = &input[lexeme.start()..lexeme.start() + lexeme.len()];
                    s.push_str(&format!("{} {}\n", tn, lt));
                }
                Node::Nonterm{rule_idx, ref nodes} => {
                    s.push_str(&format!("{}\n", grm.rule_name(rule_idx)));
                    for x in nodes.iter().rev() {
                        st.push((indent + 1, x));
                    }
                }
            }
        }
        s
    }
}

pub(crate) type Lexemes<StorageT> = Vec<Lexeme<StorageT>>;
pub(crate) type PStack = Vec<StIdx>; // Parse stack
pub(crate) type TStack<StorageT> = Vec<Node<StorageT>>; // Parse tree stack
pub(crate) type Errors<StorageT> = Vec<ParseError<StorageT>>;

pub struct Parser<'a, StorageT: 'a + Eq + Hash> {
    pub rcvry_kind: RecoveryKind,
    pub grm: &'a YaccGrammar<StorageT>,
    pub term_cost: &'a Fn(TIdx<StorageT>) -> u8,
    pub sgraph: &'a StateGraph<StorageT>,
    pub stable: &'a StateTable<StorageT>,
    pub lexemes: &'a [Lexeme<StorageT>]
}

impl<'a, StorageT: 'static + Debug + Hash + PrimInt + Unsigned>
Parser<'a, StorageT>
where usize: AsPrimitive<StorageT>
{
    fn parse<F>(rcvry_kind: RecoveryKind,
                grm: &YaccGrammar<StorageT>,
                term_cost: F,
                sgraph: &StateGraph<StorageT>,
                stable: &StateTable<StorageT>,
                lexemes: &[Lexeme<StorageT>])
             -> Result<Node<StorageT>,
                      (Option<Node<StorageT>>, Vec<ParseError<StorageT>>)>
          where F: Fn(TIdx<StorageT>) -> u8
    {
        for tidx in grm.iter_tidxs() {
            assert!(term_cost(tidx) > 0);
        }
        let psr = Parser{rcvry_kind, grm, term_cost: &term_cost, sgraph, stable, lexemes};
        let mut pstack = vec![StIdx::from(0u32)];
        let mut tstack: Vec<Node<StorageT>> = Vec::new();
        let mut errors: Vec<ParseError<StorageT>> = Vec::new();
        let accpt = psr.lr(0, &mut pstack, &mut tstack, &mut errors);
        match (accpt, errors.is_empty()) {
            (true, true)   => Ok(tstack.drain(..).nth(0).unwrap()),
            (true, false)  => Err((Some(tstack.drain(..).nth(0).unwrap()), errors)),
            (false, false) => Err((None, errors)),
            (false, true)  => panic!("Internal error")
        }
    }

    /// Start parsing text at `la_idx` (using the lexeme in `lexeme_prefix`, if it is not `None`,
    /// as the first lexeme) up to (but excluding) `end_la_idx` (if it's specified). Parsing
    /// continues as long as possible (assuming that any errors encountered can be recovered from)
    /// unless `end_la_idx` is `None`, at which point this function returns as soon as it
    /// encounters an error.
    ///
    /// Note that if `lexeme_prefix` is specified, `la_idx` will still be incremented, and thus
    /// `end_la_idx` *must* be set to `la_idx + 1` in order that the parser doesn't skip the real
    /// lexeme at position `la_idx`.
    ///
    /// Return `true` if the parse reached an accept state (i.e. all the input was consumed,
    /// possibly after making repairs) or `false` (i.e. some of the input was not consumed, even
    /// after possibly making repairs) otherwise.
    pub fn lr(&self,
              mut la_idx: usize,
              pstack: &mut PStack,
              tstack: &mut TStack<StorageT>,
              errors: &mut Errors<StorageT>)
           -> bool
    {
        let mut recoverer = None;
        let mut recovery_budget = Duration::from_millis(RECOVERY_TIME_BUDGET);
        loop {
            let st = *pstack.last().unwrap();
            let la_tidx = self.next_tidx(la_idx);

            match self.stable.action(st, la_tidx) {
                Some(Action::Reduce(prod_id)) => {
                    let rule_idx = self.grm.prod_to_rule(prod_id);
                    let pop_idx = pstack.len() - self.grm.prod(prod_id).len();
                    let nodes = tstack.drain(pop_idx - 1..).collect::<Vec<Node<StorageT>>>();
                    tstack.push(Node::Nonterm{rule_idx, nodes});

                    pstack.drain(pop_idx..);
                    let prior = *pstack.last().unwrap();
                    pstack.push(self.stable.goto(prior, rule_idx).unwrap());
                },
                Some(Action::Shift(state_id)) => {
                    let la_lexeme = self.next_lexeme(la_idx);
                    tstack.push(Node::Term{lexeme: la_lexeme});
                    pstack.push(state_id);
                    la_idx += 1;
                },
                Some(Action::Accept) => {
                    debug_assert_eq!(la_tidx, self.grm.eof_token_idx());
                    debug_assert_eq!(tstack.len(), 1);
                    return true;
                },
                None => {
                    if recoverer.is_none() {
                        recoverer = Some(match self.rcvry_kind {
                                             RecoveryKind::CPCTPlus => cpctplus::recoverer(self),
                                             RecoveryKind::MF => mf::recoverer(self),
                                             RecoveryKind::Panic => panic::recoverer(self),
                                             RecoveryKind::None => {
                                                let la_lexeme = self.next_lexeme(la_idx);
                                                errors.push(ParseError{state_idx: st,
                                                                       lexeme_idx: la_idx,
                                                                       lexeme: la_lexeme,
                                                                       repairs: vec![]});
                                                return false;
                                             }
                                         });
                    }

                    let before = Instant::now();
                    let finish_by = before + recovery_budget;
                    let (new_la_idx, repairs) = recoverer.as_ref()
                                                         .unwrap()
                                                         .as_ref()
                                                         .recover(finish_by,
                                                                  self,
                                                                  la_idx,
                                                                  pstack,
                                                                  tstack);
                    let after = Instant::now();
                    recovery_budget = recovery_budget.checked_sub(after - before)
                                                     .unwrap_or_else(|| Duration::new(0, 0));
                    let keep_going = !repairs.is_empty();
                    let la_lexeme = self.next_lexeme(la_idx);
                    errors.push(ParseError{state_idx: st, lexeme_idx: la_idx,
                                           lexeme: la_lexeme, repairs});
                    if !keep_going {
                        return false;
                    }
                    la_idx = new_la_idx;
                }
            }
        }
    }

    /// Parse from `la_idx` up to (but excluding) `end_la_idx` mutating `pstack` as parsing occurs.
    /// Returns the index of the token it parsed up to (by definition <= end_la_idx: can be less if
    /// the input is < end_la_idx, or if an error is encountered). Does not do any form of error
    /// recovery.
    pub fn lr_upto(&self,
                   lexeme_prefix: Option<Lexeme<StorageT>>,
                   mut la_idx: usize,
                   end_la_idx: usize,
                   pstack: &mut PStack,
                   tstack: &mut Option<&mut Vec<Node<StorageT>>>)
           -> usize
    {
        assert!(lexeme_prefix.is_none() || end_la_idx == la_idx + 1);
        while la_idx != end_la_idx && la_idx <= self.lexemes.len() {
            let st = *pstack.last().unwrap();
            let la_tidx = if let Some(l) = lexeme_prefix {
                              TIdx(l.tok_id())
                          } else {
                              self.next_tidx(la_idx)
                          };

            match self.stable.action(st, la_tidx) {
                Some(Action::Reduce(prod_id)) => {
                    let rule_idx = self.grm.prod_to_rule(prod_id);
                    let pop_idx = pstack.len() - self.grm.prod(prod_id).len();
                    if let Some(ref mut tstack_uw) = *tstack {
                        let nodes = tstack_uw.drain(pop_idx - 1..).collect::<Vec<Node<StorageT>>>();
                        tstack_uw.push(Node::Nonterm{rule_idx, nodes});
                    }

                    pstack.drain(pop_idx..);
                    let prior = *pstack.last().unwrap();
                    pstack.push(self.stable.goto(prior, rule_idx).unwrap());
                },
                Some(Action::Shift(state_id)) => {
                    if let Some(ref mut tstack_uw) = *tstack {
                        let la_lexeme = if let Some(l) = lexeme_prefix {
                                            l
                                        } else {
                                            self.next_lexeme(la_idx)
                                        };
                        tstack_uw.push(Node::Term{lexeme: la_lexeme});
                    }
                    pstack.push(state_id);
                    la_idx += 1;
                },
                Some(Action::Accept) => {
                    break;
                },
                None => {
                    break;
                }
            }
        }
        la_idx
    }

    /// Return a `Lexeme` for the next lemexe (if `la_idx` == `self.lexemes.len()` this will be
    /// a lexeme constructed to look as if contains the EOF token).
    pub(crate) fn next_lexeme(&self, la_idx: usize) -> Lexeme<StorageT>
    {
        let llen = self.lexemes.len();
        debug_assert!(la_idx <= llen);
        if la_idx < llen {
            self.lexemes[la_idx]
        } else {
            // We have to artificially construct a Lexeme for the EOF lexeme.
            let last_la_end = if llen == 0 {
                    0
                } else {
                    debug_assert!(la_idx > 0);
                    let last_la = self.lexemes[la_idx - 1];
                    last_la.start() + last_la.len()
                };

            Lexeme::new(StorageT::from(u32::from(self.grm.eof_token_idx())).unwrap(), last_la_end, 0)
        }
    }

    /// Return the `TIdx` of the next lexeme (if `la_idx` == `self.lexemes.len()` this will be the
    /// EOF `TIdx`).
    pub(crate) fn next_tidx(&self, la_idx: usize) -> TIdx<StorageT> {
        let ll = self.lexemes.len();
        debug_assert!(la_idx <= ll);
        if la_idx < ll {
            TIdx(self.lexemes[la_idx].tok_id())
        } else {
            self.grm.eof_token_idx()
        }
    }

    /// Start parsing text at `la_idx` (using the lexeme in `lexeme_prefix`, if it is not `None`,
    /// as the first lexeme) up to (but excluding) `end_la_idx`. If an error is encountered, parsing
    /// immediately terminates (without recovery).
    ///
    /// Note that if `lexeme_prefix` is specified, `la_idx` will still be incremented, and thus
    /// `end_la_idx` *must* be set to `la_idx + 1` in order that the parser doesn't skip the real
    /// lexeme at position `la_idx`.
    pub(crate) fn lr_cactus(&self,
                            lexeme_prefix: Option<Lexeme<StorageT>>,
                            mut la_idx: usize,
                            end_la_idx: usize,
                            mut pstack: Cactus<StIdx>,
                            tstack: &mut Option<&mut Vec<Node<StorageT>>>)
      -> (usize, Cactus<StIdx>)
    {
        assert!(lexeme_prefix.is_none() || end_la_idx == la_idx + 1);
        while la_idx != end_la_idx {
            let st = *pstack.val().unwrap();
            let la_tidx = if let Some(l) = lexeme_prefix {
                              TIdx(l.tok_id())
                          } else {
                              self.next_tidx(la_idx)
                          };

            match self.stable.action(st, la_tidx) {
                Some(Action::Reduce(prod_id)) => {
                    let rule_idx = self.grm.prod_to_rule(prod_id);
                    let pop_num = self.grm.prod(prod_id).len();
                    if let Some(ref mut tstack_uw) = *tstack {
                        let nodes = tstack_uw.drain(pstack.len() - pop_num - 1..)
                                             .collect::<Vec<Node<StorageT>>>();
                        tstack_uw.push(Node::Nonterm{rule_idx, nodes});
                    }

                    for _ in 0..pop_num {
                        pstack = pstack.parent().unwrap();
                    }
                    let prior = *pstack.val().unwrap();
                    pstack = pstack.child(self.stable.goto(prior, rule_idx).unwrap());
                },
                Some(Action::Shift(state_id)) => {
                    if let Some(ref mut tstack_uw) = *tstack {
                        let la_lexeme = if let Some(l) = lexeme_prefix {
                                            l
                                        } else {
                                            self.next_lexeme(la_idx)
                                        };
                        tstack_uw.push(Node::Term{lexeme: la_lexeme});
                    }
                    pstack = pstack.child(state_id);
                    la_idx += 1;
                },
                Some(Action::Accept) => {
                    debug_assert_eq!(la_tidx, self.grm.eof_token_idx());
                    if let Some(ref mut tstack_uw) = *tstack {
                        debug_assert_eq!(tstack_uw.len(), 1);
                    }
                    break;
                },
                None => {
                    break;
                }
            }
        }
        (la_idx, pstack)
    }
}

pub trait Recoverer<StorageT: Hash + PrimInt + Unsigned>
{
    fn recover(&self, Instant, &Parser<StorageT>, usize, &mut PStack, &mut TStack<StorageT>)
           -> (usize, Vec<Vec<ParseRepair<StorageT>>>);
}

#[derive(Debug)]
pub enum RecoveryKind {
    CPCTPlus,
    MF,
    Panic,
    None
}

/// Parse the lexemes. On success return a parse tree. On failure, return a parse tree (if all the
/// input was consumed) or `None` otherwise, and a vector of `ParseError`s.
pub fn parse<StorageT: 'static + Debug + Hash + PrimInt + Unsigned>
           (grm: &YaccGrammar<StorageT>,
            sgraph: &StateGraph<StorageT>,
            stable: &StateTable<StorageT>,
            lexemes: &Lexemes<StorageT>)
         -> Result<Node<StorageT>,
                  (Option<Node<StorageT>>, Vec<ParseError<StorageT>>)>
      where usize: AsPrimitive<StorageT>
{
    parse_rcvry(RecoveryKind::MF, grm, |_| 1, sgraph, stable, lexemes)
}

/// Parse the lexemes, specifying a particularly type of error recovery. On success return a parse
/// tree. On failure, return a parse tree (if all the input was consumed) or `None` otherwise, and
/// a vector of `ParseError`s.
pub fn parse_rcvry
       <StorageT: 'static + Debug + Hash + PrimInt + Unsigned, F>
       (rcvry_kind: RecoveryKind,
        grm: &YaccGrammar<StorageT>,
        term_cost: F,
        sgraph: &StateGraph<StorageT>,
        stable: &StateTable<StorageT>,
        lexemes: &[Lexeme<StorageT>])
    -> Result<Node<StorageT>, (Option<Node<StorageT>>, Vec<ParseError<StorageT>>)>
    where F: Fn(TIdx<StorageT>) -> u8,
          usize: AsPrimitive<StorageT>
{
    Parser::parse(rcvry_kind, grm, term_cost, sgraph, stable, lexemes)
}

/// After a parse error is encountered, the parser attempts to find a way of recovering. Each entry
/// in the sequence of repairs is represented by a `ParseRepair`.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum ParseRepair<StorageT> {
    /// Insert a `Symbol::Term`.
    Insert(TIdx<StorageT>),
    /// Insert one of the sequences of `Symbol::Term`s.
    InsertSeq(Vec<Vec<TIdx<StorageT>>>),
    /// Delete a symbol.
    Delete,
    /// Shift a symbol.
    Shift
}

/// Records a single parse error.
#[derive(Clone, Debug, PartialEq)]
pub struct ParseError<StorageT> {
    state_idx: StIdx,
    lexeme_idx: usize,
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
    pub fn state_idx(&self) -> StIdx {
        self.state_idx
    }

    /// Return the lexeme where this error was detected.
    pub fn lexeme_idx(&self) -> usize {
        self.lexeme_idx
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
    use lrlex::{build_lex, Lexeme};
    use lrtable::{Minimiser, from_yacc};
    use num_traits::ToPrimitive;
    use super::*;

    pub(crate) fn do_parse(rcvry_kind: RecoveryKind,
                           lexs: &str,
                           grms: &str,
                           input: &str)
                       -> (YaccGrammar<u16>,
                           Result<Node<u16>, (Option<Node<u16>>,
                                              Vec<ParseError<u16>>)>)
    {
        do_parse_with_costs(rcvry_kind, lexs, grms, input, &HashMap::new())
    }

    pub(crate) fn do_parse_with_costs(rcvry_kind: RecoveryKind,
                                      lexs: &str,
                                      grms: &str,
                                      input: &str,
                                      costs: &HashMap<&str, u8>)
                                  -> (YaccGrammar<u16>,
                                      Result<Node<u16>, (Option<Node<u16>>,
                                                         Vec<ParseError<u16>>)>)
    {
        let mut lexerdef = build_lex(lexs).unwrap();
        let grm = YaccGrammar::<u16>::new_with_storaget(YaccKind::Original, grms).unwrap();
        let (sgraph, stable) = from_yacc(&grm, Minimiser::Pager).unwrap();
        {
            let rule_ids = grm.tokens_map().iter()
                                          .map(|(&n, &i)| (n, u32::from(i).to_u16().unwrap()))
                                          .collect();
            lexerdef.set_rule_ids(&rule_ids);
        }
        let lexemes = lexerdef.lexer(&input).lexemes().unwrap();
        let costs_tidx = costs.iter()
                              .map(|(k, v)| (grm.token_idx(k).unwrap(), v))
                              .collect::<HashMap<_, _>>();
        let pr = parse_rcvry(rcvry_kind,
                             &grm,
                             move |t_idx| **costs_tidx.get(&t_idx).unwrap_or(&&1),
                             &sgraph,
                             &stable,
                             &lexemes);
        (grm, pr)
    }

    fn check_parse_output(lexs: &str, grms: &str, input: &str, expected: &str) {
        let (grm, pt) = do_parse(RecoveryKind::MF, lexs, grms, input);
        assert_eq!(expected, pt.unwrap().pp(&grm, &input));
    }

    #[test]
    fn simple_parse() {
        // From p4 of https://www.cs.umd.edu/class/spring2014/cmsc430/lectures/lec07.pdf
        check_parse_output("%%
[a-zA-Z_] 'ID'
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
");
    }

    #[test]
    fn parse_empty_rules() {
        let lexs = "%%
[a-zA-Z_] 'ID'";
        let grms = "%start S
%%
S: L;
L: 'ID'
 | ;
";
        check_parse_output(&lexs, &grms, "",
"S
 L
");

        check_parse_output(&lexs, &grms, "x",
"S
 L
  ID x
");
    }

    #[test]
    fn recursive_parse() {
        let lexs = "%%
\\+ '+'
\\* '*'
[0-9]+ 'INT'
";
        let grms = "%start Expr
%%
Expr : Term '+' Expr | Term;
Term : Factor '*' Term | Factor;
Factor : 'INT';";

        check_parse_output(&lexs, &grms, "2+3*4",
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
");
        check_parse_output(&lexs, &grms, "2*3+4",
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
");
    }

    #[test]
    fn parse_error() {
        let lexs = "%%
\\( '('
\\) ')'
[a-zA-Z_][a-zA-Z_0-9]* 'ID'
";
        let grms = "%start Call
%%
Call: 'ID' '(' ')';";

        check_parse_output(&lexs, &grms, "f()",
"Call
 ID f
 ( (
 ) )
");

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
