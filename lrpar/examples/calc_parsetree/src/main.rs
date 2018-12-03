use std::io::{self, BufRead, Write};

extern crate cfgrammar;
#[macro_use]
extern crate lrlex;
#[macro_use]
extern crate lrpar;

use cfgrammar::RIdx;
use lrpar::{LexParseError, Lexer, Node};

// Using `lrlex_mod!` brings the lexer for `calc.l` into scope.
lrlex_mod!(calc_l);
// Using `lrpar_mod!` brings the lexer for `calc.l` into scope.
lrpar_mod!(calc_y);

fn main() {
    // We need to get a `LexerDef` for the `calc` language in order that we can lex input.
    let lexerdef = calc_l::lexerdef();
    let stdin = io::stdin();
    loop {
        print!(">>> ");
        io::stdout().flush().ok();
        match stdin.lock().lines().next() {
            Some(Ok(ref l)) => {
                if l.trim().is_empty() {
                    continue;
                }
                // Now we create a lexer with the `lexer` method with which we can lex an input.
                let mut lexer = lexerdef.lexer(l);
                // Pass the lexer to the parser and lex and parse the input.
                let (pt, errs) = calc_y::parse(&mut lexer);
                if let Some(pt) = pt {
                    // Success! We parsed the input and created a parse tree.
                    println!("{}", Eval::new(l).eval(&pt));
                }
                for e in errs {
                    match e {
                        LexParseError::LexError(e) => {
                            eprintln!("Lexing error at column {:?}", e.idx);
                        }
                        LexParseError::ParseError(e) => {
                            let (line, col) = lexer.line_and_col(e.lexeme());
                            assert_eq!(line, 1);
                            println!("Parsing error at column {}.", col);
                        }
                    }
                }
            }
            _ => break
        }
    }
}

struct Eval<'a> {
    s: &'a str
}

impl<'a> Eval<'a> {
    fn new(s: &'a str) -> Self {
        Eval { s }
    }

    fn eval(&self, n: &Node<u8>) -> i64 {
        match *n {
            Node::Nonterm {
                ridx: RIdx(ridx),
                ref nodes
            } if ridx == calc_y::R_EXPR => {
                if nodes.len() == 1 {
                    self.eval(&nodes[0])
                } else {
                    debug_assert_eq!(nodes.len(), 3);
                    self.eval(&nodes[0]) + self.eval(&nodes[2])
                }
            }
            Node::Nonterm {
                ridx: RIdx(ridx),
                ref nodes
            } if ridx == calc_y::R_TERM => {
                if nodes.len() == 1 {
                    self.eval(&nodes[0])
                } else {
                    debug_assert_eq!(nodes.len(), 3);
                    self.eval(&nodes[0]) * self.eval(&nodes[2])
                }
            }
            Node::Nonterm {
                ridx: RIdx(ridx),
                ref nodes
            } if ridx == calc_y::R_FACTOR => {
                if nodes.len() == 1 {
                    if let Node::Term { lexeme } = nodes[0] {
                        self.s[lexeme.start()..lexeme.end().unwrap_or(lexeme.start())]
                            .parse()
                            .unwrap()
                    } else {
                        unreachable!();
                    }
                } else {
                    debug_assert_eq!(nodes.len(), 3);
                    self.eval(&nodes[1])
                }
            }
            _ => unreachable!()
        }
    }
}
