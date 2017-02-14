use lrlex::Lexeme;
use lrtable::{Action, Grammar, RIdx, StateTable, Symbol};

pub enum Node {
    Terminal{lexeme: Lexeme},
    Nonterminal{rule_idx: RIdx, nodes: Vec<Node>}
}

#[derive(Debug)]
pub struct ParseError;

impl Node {
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
                &Node::Terminal{lexeme: Lexeme{tok_id, start, len}} => {
                    s.push_str(&format!("{} {}\n", grm.terminal_names.get(tok_id).unwrap(), &input[start..start + len]));
                }
                &Node::Nonterminal{rule_idx, ref nodes} => {
                    s.push_str(&format!("{}\n", grm.nonterminal_names.get(rule_idx).unwrap()));
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
pub fn parse(grm: &Grammar, stable: &StateTable, lexemes: &Vec<Lexeme>) -> Result<Node, ParseError> {
    let mut lexemes_iter = lexemes.iter();
    // Instead of having a single stack, which we'd then have to invent a new struct / tuple for,
    // it's easiest to split the parse and parse tree stack into two.
    let mut pstack = vec![0]; // Parse stack
    let mut tstack: Vec<Node> = Vec::new(); // Parse tree stack
    let mut la = lexemes_iter.next().unwrap();
    loop {
        let st = *pstack.last().unwrap();
        match stable.actions.get(&(st, Symbol::Terminal(la.tok_id))) {
            Some(&Action::Reduce(prod_id)) => {
                let rule_idx = grm.prod_to_rule_idx(prod_id);
                let pop_idx = pstack.len() - grm.prods.get(prod_id).unwrap().len();
                let nodes = tstack.drain(pop_idx - 1..).collect::<Vec<Node>>();
                tstack.push(Node::Nonterminal{rule_idx: rule_idx, nodes: nodes});

                pstack.drain(pop_idx..);
                let prior = *pstack.last().unwrap();
                pstack.push(*stable.gotos.get(&(prior, rule_idx)).unwrap());
            },
            Some(&Action::Shift(state_id)) => {
                tstack.push(Node::Terminal{lexeme: *la});
                la = lexemes_iter.next().unwrap();
                pstack.push(state_id);
            },
            Some(&Action::Accept) => {
                debug_assert_eq!(la.tok_id, grm.end_term);
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
    use lrlex::{build_lex, do_lex, Lexeme};
    use lrtable::yacc_to_statetable;
    use super::*;

    fn check_parse_output(lexs: &str, grms: &str, input: &str, expected: &str) {
        let (grm, stable) = yacc_to_statetable(grms).unwrap();
        let mut lexer = build_lex(lexs).unwrap();
        let mut rule_ids = HashMap::<&str, usize>::new();
        for (i, n) in grm.terminal_names.iter().enumerate() {
            rule_ids.insert(&*n, i);
        }
        lexer.set_rule_ids(&rule_ids);
        let mut lexemes = do_lex(&lexer, &input).unwrap();
        lexemes.push(Lexeme{tok_id: grm.end_term, start: input.len(), len: 0});
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
