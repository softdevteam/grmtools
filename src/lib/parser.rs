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

#[derive(Debug)]
pub enum Node<TokId> {
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

/// Parse the lexemes into a parse tree.
pub fn parse<TokId: Copy + TryFrom<usize> + TryInto<usize>>
            (grm: &YaccGrammar, stable: &StateTable, lexemes: &Vec<Lexeme<TokId>>)
         -> Result<Node<TokId>, Vec<ParseError<TokId>>>
{
    let mut lexemes_iter = lexemes.iter();
    // Instead of having a single stack, which we'd then have to invent a new struct / tuple for,
    // it's easiest to split the parse and parse tree stack into two.
    let mut pstack = vec![StIdx::from(0)]; // Parse stack
    let mut tstack: Vec<Node<TokId>> = Vec::new(); // Parse tree stack
    let mut la = lexemes_iter.next();
    let mut last_la_end = 0;
    loop {
        let st = *pstack.last().unwrap();
        let la_term = match la {
            Some(t) => {
                last_la_end = t.start() + t.len();
                Symbol::Term(TIdx::from(t.tok_id().try_into().ok().unwrap()))
            }
            None => Symbol::Term(TIdx::from(grm.eof_term_idx()))
        };
        match stable.action(st, la_term) {
            Some(Action::Reduce(prod_id)) => {
                let nonterm_idx = grm.prod_to_nonterm(prod_id);
                let pop_idx = pstack.len() - grm.prod(prod_id).unwrap().len();
                let nodes = tstack.drain(pop_idx - 1..).collect::<Vec<Node<TokId>>>();
                tstack.push(Node::Nonterm{nonterm_idx: nonterm_idx, nodes: nodes});

                pstack.drain(pop_idx..);
                let prior = *pstack.last().unwrap();
                pstack.push(stable.goto(prior, NTIdx::from(nonterm_idx)).unwrap());
            },
            Some(Action::Shift(state_id)) => {
                tstack.push(Node::Term{lexeme: *la.unwrap()});
                la = lexemes_iter.next();
                pstack.push(state_id);
            },
            Some(Action::Accept) => {
                debug_assert_eq!(la_term, Symbol::Term(TIdx::from(grm.eof_term_idx())));
                debug_assert_eq!(tstack.len(), 1);
                return Ok(tstack.drain(..).nth(0).unwrap());
            },
            None => {
                let err_la = match la {
                    Some(x) => *x,
                    None => {
                        Lexeme::new(TokId::try_from(usize::from(grm.eof_term_idx()))
                                          .ok()
                                          .unwrap(),
                                    last_la_end, 0)
                    }
                };
                return Err(vec![ParseError{state_idx: st, lexeme: err_la}]);
            }
        }
    }
}

/// Records a single parse error.
#[derive(Debug, PartialEq)]
pub struct ParseError<TokId> {
    state_idx: StIdx,
    lexeme: Lexeme<TokId>
}

impl<TokId> ParseError<TokId> {
    /// Return the state table index where this error was detected.
    pub fn state_idx(&self) -> StIdx {
        self.state_idx
    }

    /// Return the lexeme where this error was detected.
    pub fn lexeme(&self) -> &Lexeme<TokId> {
        &self.lexeme
    }
}

#[cfg(test)]
mod test {
    use std::convert::TryFrom;
    use cfgrammar::yacc::{YaccGrammar, yacc_grm, YaccKind};
    use lrlex::{build_lex, Lexeme};
    use lrtable::{Minimiser, yacc_to_statetable};
    use super::*;

    fn do_parse(lexs: &str, grms: &str, input: &str) -> (YaccGrammar, Result<Node<u16>, Vec<ParseError<u16>>>) {
        let mut lexerdef = build_lex(lexs).unwrap();
        let grm = yacc_grm(YaccKind::Original, grms).unwrap();
        let stable = yacc_to_statetable(&grm, Minimiser::Pager).unwrap();
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
