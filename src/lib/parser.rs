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

use std::convert::{TryFrom, TryInto};

use cactus::Cactus;
use cfgrammar::{NTIdx, Symbol, TIdx};
use cfgrammar::yacc::YaccGrammar;
use lrlex::Lexeme;
use lrtable::{Action, StateGraph, StateTable, StIdx};

use kimyi;
use kimyi_plus;
use mf;
use corchuelo;

#[derive(Debug, Clone, PartialEq)]
pub enum Node<TokId: Copy> {
    Term{lexeme: Lexeme<TokId>},
    Nonterm{nonterm_idx: NTIdx, nodes: Vec<Node<TokId>>}
}

impl<TokId: Copy + TryInto<usize>> Node<TokId> {
    /// Return a pretty-printed version of this node.
    pub fn pp(&self, grm: &YaccGrammar, input: &str) -> String {
        let mut st = vec![(0, self)]; // Stack of (indent level, node) pairs
        let mut s = String::new();
        while !st.is_empty() {
            let (indent, e) = st.pop().unwrap();
            for _ in 0..indent {
                s.push_str(" ");
            }
            match *e {
                Node::Term{lexeme} => {
                    let tn = grm.term_name(TIdx::from(lexeme.tok_id().try_into().ok().unwrap())).unwrap();
                    let lt = &input[lexeme.start()..lexeme.start() + lexeme.len()];
                    s.push_str(&format!("{} {}\n", tn, lt));
                }
                Node::Nonterm{nonterm_idx, ref nodes} => {
                    s.push_str(&format!("{}\n", grm.nonterm_name(nonterm_idx)));
                    for x in nodes.iter().rev() {
                        st.push((indent + 1, x));
                    }
                }
            }
        }
        s
    }
}

pub(crate) type Lexemes<TokId> = Vec<Lexeme<TokId>>;
pub(crate) type PStack = Vec<StIdx>; // Parse stack
pub(crate) type TStack<TokId> = Vec<Node<TokId>>; // Parse tree stack
pub(crate) type Errors<TokId> = Vec<ParseError<TokId>>;

pub struct Parser<'a, TokId: Clone + Copy + TryFrom<usize> + TryInto<usize>> where TokId: 'a {
    pub rcvry_kind: RecoveryKind,
    pub grm: &'a YaccGrammar,
    pub ic: &'a Fn(TIdx) -> u64,
    pub dc: &'a Fn(TIdx) -> u64,
    pub sgraph: &'a StateGraph,
    pub stable: &'a StateTable,
    pub lexemes: &'a Lexemes<TokId>
}

use std::fmt::Debug;
impl<'a, TokId: Clone + Copy + Debug + PartialEq + TryFrom<usize> + TryInto<usize>> Parser<'a, TokId> {
    fn parse<F, G>(rcvry_kind: RecoveryKind,
             grm: &YaccGrammar,
             ic: F,
             dc: G,
             sgraph: &StateGraph,
             stable: &StateTable,
             lexemes: &Lexemes<TokId>)
          -> Result<Node<TokId>, (Option<Node<TokId>>, Vec<ParseError<TokId>>)>
      where F: Fn(TIdx) -> u64,
            G: Fn(TIdx) -> u64
    {
        let psr = Parser{rcvry_kind, grm, ic: &ic, dc: &dc, sgraph, stable, lexemes};
        let mut pstack = vec![StIdx::from(0)];
        let mut tstack: Vec<Node<TokId>> = Vec::new();
        let mut errors: Vec<ParseError<TokId>> = Vec::new();
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
    pub fn lr(&self, mut la_idx: usize, pstack: &mut PStack, tstack: &mut TStack<TokId>,
              errors: &mut Errors<TokId>)
           -> bool
    {
        let mut recoverer = None;
        loop {
            let st = *pstack.last().unwrap();
            let (la_lexeme, la_term) = self.next_lexeme(None, la_idx);

            match self.stable.action(st, la_term) {
                Some(Action::Reduce(prod_id)) => {
                    let nonterm_idx = self.grm.prod_to_nonterm(prod_id);
                    let pop_idx = pstack.len() - self.grm.prod(prod_id).len();
                    let nodes = tstack.drain(pop_idx - 1..).collect::<Vec<Node<TokId>>>();
                    tstack.push(Node::Nonterm{nonterm_idx: nonterm_idx, nodes: nodes});

                    pstack.drain(pop_idx..);
                    let prior = *pstack.last().unwrap();
                    pstack.push(self.stable.goto(prior, NTIdx::from(nonterm_idx)).unwrap());
                },
                Some(Action::Shift(state_id)) => {
                    tstack.push(Node::Term{lexeme: la_lexeme});
                    pstack.push(state_id);
                    la_idx += 1;
                },
                Some(Action::Accept) => {
                    debug_assert_eq!(la_term, Symbol::Term(TIdx::from(self.grm.eof_term_idx())));
                    debug_assert_eq!(tstack.len(), 1);
                    return true;
                },
                None => {
                    if recoverer.is_none() {
                        recoverer = Some(match self.rcvry_kind {
                                             RecoveryKind::Corchuelo => corchuelo::recoverer(),
                                             RecoveryKind::KimYi =>
                                                 kimyi::recoverer(&self),
                                             RecoveryKind::KimYiPlus =>
                                                 kimyi_plus::recoverer(&self),
                                             RecoveryKind::MF =>
                                                 mf::recoverer(&self),
                                         });
                    }

                    let (new_la_idx, repairs) = recoverer.as_ref()
                                                         .unwrap()
                                                         .as_ref()
                                                         .recover(&self, la_idx, pstack, tstack);
                    let keep_going = repairs.len() != 0;
                    errors.push(ParseError{state_idx: st, lexeme_idx: la_idx,
                                           lexeme: la_lexeme, repairs: repairs});
                    if !keep_going {
                        return false;
                    }
                    la_idx = new_la_idx;
                }
            }
        }
    }

    /// Return a (`Lexeme`, `Symbol::Term`) pair of the next lemexe. When `lexeme_prefix` is not
    /// `None`, that is the next lexeme. Otherwise it will be the next lexeme in `self.lexemes` or
    /// a specially constructed lexeme representing EOF.
    pub(crate) fn next_lexeme(&self, lexemes_prefix: Option<Lexeme<TokId>>, la_idx: usize)
                          -> (Lexeme<TokId>, Symbol)
    {
        if let Some(l) = lexemes_prefix {
            (l, Symbol::Term(TIdx::from(l.tok_id().try_into().ok().unwrap())))
        } else if let Some(l) = self.lexemes.get(la_idx) {
            (*l, Symbol::Term(TIdx::from(l.tok_id().try_into().ok().unwrap())))
        } else {
            // We have to artificially construct a Lexeme for the EOF lexeme.
            debug_assert_eq!(la_idx, self.lexemes.len());
            let last_la_end;
            if self.lexemes.len() == 0 {
                last_la_end = 0;
            } else {
                debug_assert!(la_idx > 0);
                let last_la = self.lexemes[la_idx - 1];
                last_la_end = last_la.start() + last_la.len();
            }
            let la_lexeme = Lexeme::new(TokId::try_from(usize::from(self.grm.eof_term_idx()))
                                              .ok()
                                              .unwrap(),
                                        last_la_end, 0);

            (la_lexeme, Symbol::Term(TIdx::from(self.grm.eof_term_idx())))
        }
    }

    /// What is the deletion cost of `sym`?
    pub(crate) fn dc(&self, sym: Symbol) -> u64 {
        match sym {
            Symbol::Term(t_idx) => (self.dc)(t_idx),
            _ => panic!("Internal error")
        }
    }

    /// What is the insertion cost of `sym`?
    pub(crate) fn ic(&self, _: Symbol) -> u64 {
        1
    }

    /// Start parsing text at `la_idx` (using the lexeme in `lexeme_prefix`, if it is not `None`,
    /// as the first lexeme) up to (but excluding) `end_la_idx`. If an error is encountered, parsing
    /// immediately terminates (without recovery).
    ///
    /// Note that if `lexeme_prefix` is specified, `la_idx` will still be incremented, and thus
    /// `end_la_idx` *must* be set to `la_idx + 1` in order that the parser doesn't skip the real
    /// lexeme at position `la_idx`.
    pub(crate) fn lr_cactus(&self,
                            lexeme_prefix: Option<Lexeme<TokId>>,
                            mut la_idx: usize,
                            end_la_idx: usize,
                            mut pstack: Cactus<StIdx>,
                            tstack: &mut Option<&mut Vec<Node<TokId>>>)
      -> (usize, Cactus<StIdx>)
    {
        assert!(lexeme_prefix.is_none() || end_la_idx == la_idx + 1);
        while la_idx != end_la_idx {
            let st = *pstack.val().unwrap();
            let (la_lexeme, la_term) = self.next_lexeme(lexeme_prefix, la_idx);

            match self.stable.action(st, la_term) {
                Some(Action::Reduce(prod_id)) => {
                    let nonterm_idx = self.grm.prod_to_nonterm(prod_id);
                    let pop_num = self.grm.prod(prod_id).len();
                    if let &mut Some(ref mut tstack_uw) = tstack {
                        let nodes = tstack_uw.drain(pstack.len() - pop_num - 1..)
                                             .collect::<Vec<Node<TokId>>>();
                        tstack_uw.push(Node::Nonterm{nonterm_idx: nonterm_idx, nodes: nodes});
                    }

                    for _ in 0..pop_num {
                        pstack = pstack.parent().unwrap();
                    }
                    let prior = *pstack.val().unwrap();
                    pstack = pstack.child(self.stable.goto(prior, NTIdx::from(nonterm_idx)).unwrap());
                },
                Some(Action::Shift(state_id)) => {
                    if let &mut Some(ref mut tstack_uw) = tstack {
                        tstack_uw.push(Node::Term{lexeme: la_lexeme});
                    }
                    pstack = pstack.child(state_id);
                    la_idx += 1;
                },
                Some(Action::Accept) => {
                    debug_assert_eq!(la_term, Symbol::Term(TIdx::from(self.grm.eof_term_idx())));
                    if let &mut Some(ref mut tstack_uw) = tstack {
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

pub trait Recoverer<TokId: Clone + Copy + Debug + TryFrom<usize> + TryInto<usize> + PartialEq> {
    fn recover(&self, &Parser<TokId>, usize, &mut PStack, &mut TStack<TokId>)
           -> (usize, Vec<Vec<ParseRepair>>);
}

pub enum RecoveryKind {
    Corchuelo,
    KimYi,
    KimYiPlus,
    MF
}

/// Parse the lexemes. On success return a parse tree. On failure, return a parse tree (if all the
/// input was consumed) or `None` otherwise, and a vector of `ParseError`s.
pub fn parse<TokId: Copy + Debug + PartialEq + TryFrom<usize> + TryInto<usize>>
       (grm: &YaccGrammar, sgraph: &StateGraph, stable: &StateTable,
        lexemes: &Vec<Lexeme<TokId>>)
    -> Result<Node<TokId>, (Option<Node<TokId>>, Vec<ParseError<TokId>>)>
{
    parse_rcvry(RecoveryKind::KimYi, grm, |_| 1, |_| 1, sgraph, stable, lexemes)
}

/// Parse the lexemes, specifying a particularly type of error recovery. On success return a parse
/// tree. On failure, return a parse tree (if all the input was consumed) or `None` otherwise, and
/// a vector of `ParseError`s.
pub fn parse_rcvry
       <TokId: Copy + Debug + PartialEq + TryFrom<usize> + TryInto<usize>, F, G>
       (rcvry_kind: RecoveryKind,
        grm: &YaccGrammar,
        ic: F,
        dc: G,
        sgraph: &StateGraph,
        stable: &StateTable,
        lexemes: &Vec<Lexeme<TokId>>)
    -> Result<Node<TokId>, (Option<Node<TokId>>, Vec<ParseError<TokId>>)>
    where F: Fn(TIdx) -> u64, G: Fn(TIdx) -> u64
{
    Parser::parse(rcvry_kind, grm, ic, dc, sgraph, stable, lexemes)
}

/// After a parse error is encountered, the parser attempts to find a way of recovering. Each entry
/// in the sequence of repairs is represented by a `ParseRepair`.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum ParseRepair {
    /// Insert a `Symbol::Term`.
    Insert(TIdx),
    /// Insert one of the sequences of `Symbol::Term`s.
    InsertSeq(Vec<Vec<TIdx>>),
    /// Delete a symbol.
    Delete,
    /// Shift a symbol.
    Shift
}

/// Records a single parse error.
#[derive(Clone, Debug, PartialEq)]
pub struct ParseError<TokId: Copy> {
    state_idx: StIdx,
    lexeme_idx: usize,
    lexeme: Lexeme<TokId>,
    repairs: Vec<Vec<ParseRepair>>
}

impl<TokId: Copy> ParseError<TokId> {
    /// Return the state table index where this error was detected.
    pub fn state_idx(&self) -> StIdx {
        self.state_idx
    }

    /// Return the lexeme where this error was detected.
    pub fn lexeme_idx(&self) -> usize {
        self.lexeme_idx
    }

    /// Return the lexeme where this error was detected.
    pub fn lexeme(&self) -> &Lexeme<TokId> {
        &self.lexeme
    }

    /// Return the repairs found that would fix this error. Note that there are infinite number of
    /// possible repairs for any error, so this is by definition a (finite) subset.
    pub fn repairs(&self) -> &Vec<Vec<ParseRepair>> {
        &self.repairs
    }
}

#[cfg(test)]
pub(crate) mod test {
    use std::convert::TryFrom;
    use cfgrammar::yacc::{YaccGrammar, yacc_grm, YaccKind};
    use lrlex::{build_lex, Lexeme};
    use lrtable::{Minimiser, from_yacc};
    use super::*;

    pub(crate) fn do_parse(rcvry_kind: RecoveryKind, lexs: &str, grms: &str, input: &str)
                       -> (YaccGrammar, Result<Node<u16>, (Option<Node<u16>>, Vec<ParseError<u16>>)>)
    {
        let mut lexerdef = build_lex(lexs).unwrap();
        let grm = yacc_grm(YaccKind::Original, grms).unwrap();
        let (sgraph, stable) = from_yacc(&grm, Minimiser::Pager).unwrap();
        {
            let rule_ids = grm.terms_map().iter()
                                          .map(|(&n, &i)| (n, u16::try_from(usize::from(i)).unwrap()))
                                          .collect();
            lexerdef.set_rule_ids(&rule_ids);
        }
        let lexemes = lexerdef.lexer(&input).lexemes().unwrap();
        let pr = parse_rcvry(rcvry_kind, &grm, |_| 1, |_| 1, &sgraph, &stable, &lexemes);
        (grm, pr)
    }

    fn check_parse_output(lexs: &str, grms: &str, input: &str, expected: &str) {
        let (grm, pt) = do_parse(RecoveryKind::KimYi, lexs, grms, input);
        assert_eq!(expected, pt.unwrap().pp(&grm, &input));
    }

    #[test]
    fn simple_parse() {
        // From p4 of https://www.cs.umd.edu/class/spring2014/cmsc430/lectures/lec07.pdf
        check_parse_output("%%
[a-zA-Z_] ID
[+] PLUS",
"
%start E
%%
E: T 'PLUS' E
 | T;
T: 'ID';
",
"a+b",
"E
 T
  ID a
 PLUS +
 E
  T
   ID b
");
    }

    #[test]
    fn parse_empty_rules() {
        let lexs = "%%
[a-zA-Z_] ID";
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
[+] PLUS
[*] MULT
[0-9]+ INT
";
        let grms = "%start Expr
%%
Expr : Term 'PLUS' Expr | Term;
Term : Factor 'MULT' Term | Factor;
Factor : 'INT';";

        check_parse_output(&lexs, &grms, "2+3*4",
"Expr
 Term
  Factor
   INT 2
 PLUS +
 Expr
  Term
   Factor
    INT 3
   MULT *
   Term
    Factor
     INT 4
");
        check_parse_output(&lexs, &grms, "2*3+4",
"Expr
 Term
  Factor
   INT 2
  MULT *
  Term
   Factor
    INT 3
 PLUS +
 Expr
  Term
   Factor
    INT 4
");
    }

    #[test]
    fn parse_error() {
        let lexs = "%%
[(] OPEN_BRACKET
[)] CLOSE_BRACKET
[a-zA-Z_][a-zA-Z_0-9]* ID
";
        let grms = "%start Call
%%
Call: 'ID' 'OPEN_BRACKET' 'CLOSE_BRACKET';";

        check_parse_output(&lexs, &grms, "f()",
"Call
 ID f
 OPEN_BRACKET (
 CLOSE_BRACKET )
");

        let (grm, pr) = do_parse(RecoveryKind::KimYi, &lexs, &grms, "f(");
        let (_, errs) = pr.unwrap_err();
        assert_eq!(errs.len(), 1);
        let err_tok_id = u16::try_from(usize::from(grm.eof_term_idx())).ok().unwrap();
        assert_eq!(errs[0].lexeme(), &Lexeme::new(err_tok_id, 2, 0));

        let (grm, pr) = do_parse(RecoveryKind::KimYi, &lexs, &grms, "f(f(");
        let (_, errs) = pr.unwrap_err();
        assert_eq!(errs.len(), 1);
        let err_tok_id = u16::try_from(usize::from(grm.term_idx("ID").unwrap())).ok().unwrap();
        assert_eq!(errs[0].lexeme(), &Lexeme::new(err_tok_id, 2, 1));
     }

    #[test]
    fn no_tree_if_cant_be_repaired() {
        let lexs = "%%
a A
b B
";
        let grms = "%start S
%%
S: 'A' 'A' 'B';
";

        let us = "aaaaaaaaaaaaaab";
        let (_, pr) = do_parse(RecoveryKind::KimYiPlus, &lexs, &grms, &us);
        assert!(pr.is_err() && pr.unwrap_err().0.is_none());
    }
}
