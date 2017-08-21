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

use cfgrammar::{NTIdx, Symbol, TIdx};
use cfgrammar::yacc::YaccGrammar;
use lrlex::Lexeme;
use lrtable::{Action, StateTable, StIdx};

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
                    s.push_str(&format!("{}\n", grm.nonterm_name(nonterm_idx).unwrap()));
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

pub(crate) struct Parser<'a, TokId: Clone + Copy + TryFrom<usize> + TryInto<usize>> where TokId: 'a {
    pub grm: &'a YaccGrammar,
    pub stable: &'a StateTable,
    pub lexemes: &'a Lexemes<TokId>
}

use std::fmt::Debug;
impl<'a, TokId: Clone + Copy + Debug + PartialEq + TryFrom<usize> + TryInto<usize>> Parser<'a, TokId> {
    fn parse(grm: &YaccGrammar, stable: &StateTable, lexemes: &Lexemes<TokId>)
         -> Result<Node<TokId>, Vec<ParseError<TokId>>>
    {
        let psr = Parser{grm, stable, lexemes};
        let mut pstack = vec![StIdx::from(0)];
        let mut tstack: Vec<Node<TokId>> = Vec::new();
        let mut errors: Vec<ParseError<TokId>> = Vec::new();
        psr.lr(0, &mut pstack, &mut tstack, &mut errors);
        if !errors.is_empty() {
            Err(errors)
        } else {
            Ok(tstack.drain(..).nth(0).unwrap())
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
    pub(crate) fn lr(&self, mut la_idx: usize, pstack: &mut PStack, tstack: &mut TStack<TokId>,
                     errors: &mut Errors<TokId>)
                  -> usize
    {
        loop {
            let st = *pstack.last().unwrap();
            let (la_lexeme, la_term) = self.next_lexeme(None, la_idx);

            match self.stable.action(st, la_term) {
                Some(Action::Reduce(prod_id)) => {
                    let nonterm_idx = self.grm.prod_to_nonterm(prod_id);
                    let pop_idx = pstack.len() - self.grm.prod(prod_id).unwrap().len();
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
                    break;
                },
                None => {
                    let (new_la_idx, repairs) = corchuelo::recover(self, la_idx, pstack, tstack);
                    let keep_going = repairs.len() != 0;
                    errors.push(ParseError{state_idx: st, lexeme_idx: la_idx,
                                           lexeme: la_lexeme, repairs: repairs});
                    if !keep_going {
                        break;
                    }
                    la_idx = new_la_idx;
                }
            }
        }
        la_idx
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
}

/// Parse the lexemes, returning either a parse tree or a vector of `ParseError`s.
pub fn parse<TokId: Copy + Debug + PartialEq + TryFrom<usize> + TryInto<usize>>
            (grm: &YaccGrammar, stable: &StateTable, lexemes: &Vec<Lexeme<TokId>>)
         -> Result<Node<TokId>, Vec<ParseError<TokId>>>
{
    Parser::parse(grm, stable, lexemes)
}

/// After a parse error is encountered, the parser attempts to find a way of recovering. Each entry
/// in the sequence of repairs is represented by a `ParseRepair`.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum ParseRepair {
    /// Insert a `Symbol::Term` with idx `term_idx`.
    Insert{term_idx: TIdx},
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

    pub(crate) fn do_parse(lexs: &str, grms: &str, input: &str) -> (YaccGrammar, Result<Node<u16>, Vec<ParseError<u16>>>) {
        let mut lexerdef = build_lex(lexs).unwrap();
        let grm = yacc_grm(YaccKind::Original, grms).unwrap();
        let (_, stable) = from_yacc(&grm, Minimiser::Pager).unwrap();
        {
            let rule_ids = grm.terms_map().iter()
                                          .map(|(&n, &i)| (n, u16::try_from(usize::from(i)).unwrap()))
                                          .collect();
            lexerdef.set_rule_ids(&rule_ids);
        }
        let lexemes = lexerdef.lexer(&input).lexemes().unwrap();
        let pr = parse(&grm, &stable, &lexemes);
        (grm, pr)
    }

    fn check_parse_output(lexs: &str, grms: &str, input: &str, expected: &str) {
        let (grm, pt) = do_parse(lexs, grms, input);
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

        let (grm, pr) = do_parse(&lexs, &grms, "f(");
        let errs = pr.unwrap_err();
        assert_eq!(errs.len(), 1);
        let err_tok_id = u16::try_from(usize::from(grm.eof_term_idx())).ok().unwrap();
        assert_eq!(errs[0].lexeme(), &Lexeme::new(err_tok_id, 2, 0));

        let (grm, pr) = do_parse(&lexs, &grms, "f(f(");
        let errs = pr.unwrap_err();
        assert_eq!(errs.len(), 1);
        let err_tok_id = u16::try_from(usize::from(grm.term_idx("ID").unwrap())).ok().unwrap();
        assert_eq!(errs[0].lexeme(), &Lexeme::new(err_tok_id, 2, 1));
     }
}
