use std::convert::TryInto;

use lrlex::Lexeme;
use lrtable::{Action, Grammar, NTIdx, StateTable, StIdx, Symbol, TIdx};

pub enum Node<TokId> {
    Terminal{lexeme: Lexeme<TokId>},
    Nonterminal{nonterm_idx: NTIdx, nodes: Vec<Node<TokId>>}
}

#[derive(Debug)]
pub struct ParseError;

impl<TokId: Copy + TryInto<usize>> Node<TokId> {
    /// Return a pretty-printed version of this node.
    pub fn pp(&self, grm: &Grammar, input: &str) -> String {
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
pub fn parse<TokId: Copy + TryInto<usize>>(grm: &Grammar, stable: &StateTable, lexemes:
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
                debug_assert_eq!(TIdx::from(la.tok_id().try_into().ok().unwrap()), grm.end_term);
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
    use lrtable::yacc_to_statetable;
    use super::*;

    fn check_parse_output(lexs: &str, grms: &str, input: &str, expected: &str) {
        let (grm, stable) = yacc_to_statetable(grms).unwrap();
        let mut lexer = build_lex(lexs).unwrap();
        let mut rule_ids = HashMap::<&str, usize>::new();
        for term_idx in grm.iter_term_idxs() {
            rule_ids.insert(grm.term_name(term_idx).unwrap(), usize::from(term_idx));
        }
        lexer.set_rule_ids(&rule_ids);
        let mut lexemes = lexer.lex(&input).unwrap();
        lexemes.push(Lexeme::new(usize::from(grm.end_term), input.len(), 0));
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
