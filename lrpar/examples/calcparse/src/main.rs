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
                match calc_y::parse(&mut lexer) {
                    // Success! We parsed the input and created a parse tree.
                    Ok(pt) => println!("{}", Eval::new(l).eval(&pt)),
                    // We weren't able to fully lex the input, so all we can do is tell the user
                    // at what index the lexer gave up at.
                    Err(LexParseError::LexError(e)) => {
                        println!("Lexing error at column {:?}", e.idx)
                    }
                    // Parsing failed, but with the help of error recovery a parse tree was
                    // produced. However, we simply report the error to the user and don't attempt
                    // to do any sort of evaluation.
                    Err(LexParseError::ParseError(_, errs)) => {
                        // One or more errors were detected during parsing.
                        for e in errs {
                            let (line, col) = lexer.line_and_col(e.lexeme()).unwrap();
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
                        self.s[lexeme.start()..lexeme.end()].parse().unwrap()
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
