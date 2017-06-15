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

use std::convert::TryInto;

use cfgrammar::{NTIdx, Symbol, TIdx};
use cfgrammar::yacc::YaccGrammar;
use lrlex::Lexeme;
use lrtable::{Action, StateTable, StIdx};

pub enum Node<TokId> {
    Terminal{lexeme: Lexeme<TokId>},
    Nonterminal{nonterm_idx: NTIdx, nodes: Vec<Node<TokId>>}
}

#[derive(Debug)]
pub struct ParseError;

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
            match e {
                &Node::Terminal{lexeme} => {
                    let tn = grm.term_name(TIdx::from(lexeme.tok_id().try_into().ok().unwrap())).unwrap();
                    let lt = &input[lexeme.start()..lexeme.start() + lexeme.len()];
                    s.push_str(&format!("{} {}\n", tn, lt));
                }
                &Node::Nonterminal{nonterm_idx, ref nodes} => {
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
pub fn parse<TokId: Copy + TryInto<usize>>(grm: &YaccGrammar, stable: &StateTable, lexemes:
                                        &Vec<Lexeme<TokId>>) -> Result<Node<TokId>, ParseError>
{
    let mut lexemes_iter = lexemes.iter();
    // Instead of having a single stack, which we'd then have to invent a new struct / tuple for,
    // it's easiest to split the parse and parse tree stack into two.
    let mut pstack = vec![StIdx::from(0)]; // Parse stack
    let mut tstack: Vec<Node<TokId>> = Vec::new(); // Parse tree stack
    let mut la = lexemes_iter.next().unwrap();
    loop {
        let st = *pstack.last().unwrap();
        match stable.action(st, Symbol::Terminal(TIdx::from(la.tok_id().try_into().ok().unwrap()))) {
            Some(Action::Reduce(prod_id)) => {
                let nonterm_idx = grm.prod_to_nonterm(prod_id);
                let pop_idx = pstack.len() - grm.prod(prod_id).unwrap().len();
                let nodes = tstack.drain(pop_idx - 1..).collect::<Vec<Node<TokId>>>();
                tstack.push(Node::Nonterminal{nonterm_idx: nonterm_idx, nodes: nodes});

                pstack.drain(pop_idx..);
                let prior = *pstack.last().unwrap();
                pstack.push(stable.goto(prior, NTIdx::from(nonterm_idx)).unwrap());
            },
            Some(Action::Shift(state_id)) => {
                tstack.push(Node::Terminal{lexeme: *la});
                la = lexemes_iter.next().unwrap();
                pstack.push(state_id);
            },
            Some(Action::Accept) => {
                debug_assert_eq!(TIdx::from(la.tok_id().try_into().ok().unwrap()), grm.end_term_idx());
                debug_assert_eq!(tstack.len(), 1);
                return Ok(tstack.drain(..).nth(0).unwrap());
            },
            _ => {
                return Err(ParseError);
            }
        }
    }
}

#[cfg(test)]
mod test {
    use std::collections::HashMap;
    use lrlex::{build_lex, Lexeme};
    use lrtable::{Minimiser, yacc_to_statetable};
    use super::*;

    fn check_parse_output(lexs: &str, grms: &str, input: &str, expected: &str) {
        let (grm, stable) = yacc_to_statetable(grms, Minimiser::Pager).unwrap();
        let mut lexerdef = build_lex(lexs).unwrap();
        let mut rule_ids = HashMap::<&str, usize>::new();
        for term_idx in grm.iter_term_idxs() {
            rule_ids.insert(grm.term_name(term_idx).unwrap(), usize::from(term_idx));
        }
        lexerdef.set_rule_ids(&rule_ids);
        let mut lexemes = lexerdef.lexer(&input).lexemes().unwrap();
        lexemes.push(Lexeme::new(usize::from(grm.end_term_idx()), input.len(), 0));
        let pt = parse(&grm, &stable, &lexemes).unwrap();
        assert_eq!(expected, pt.pp(&grm, &input));
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
}
