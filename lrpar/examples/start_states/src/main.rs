use std::io::{self, BufRead, Write};

use cfgrammar::RIdx;
use lrlex::{lrlex_mod, DefaultLexeme};
use lrpar::{lrpar_mod, Lexeme, Node};

// Using `lrlex_mod!` brings the lexer for `comment.l` into scope. By default the module name will be
// `comment_l` (i.e. the file name, minus any extensions, with a suffix of `_l`).
lrlex_mod!("comment.l");
// Using `lrpar_mod!` brings the parser for `comment.y` into scope. By default the module name will be
// `comment_y` (i.e. the file name, minus any extensions, with a suffix of `_y`).
lrpar_mod!("comment.y");

fn main() {
    // Get the `LexerDef` for the `comment` language.
    let lexerdef = comment_l::lexerdef();
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
                let lexer = lexerdef.lexer(l);
                // Pass the lexer to the parser and lex and parse the input.
                let (pt, errs) = comment_y::parse(&lexer);
                for e in errs {
                    println!("{}", e.pp(&lexer, &comment_y::token_epp));
                }
                if let Some(pt) = pt {
                    // Success! We parsed the input and created a parse tree.
                    println!("Result: {}", Eval::new(l).eval(&pt));
                }
            }
            _ => break,
        }
    }
}

struct Eval<'a> {
    s: &'a str,
}

impl<'a> Eval<'a> {
    fn new(s: &'a str) -> Self {
        Eval { s }
    }

    fn eval(&self, n: &Node<DefaultLexeme<u32>, u32>) -> String {
        match *n {
            Node::Nonterm {
                ridx: RIdx(ridx),
                ref nodes,
            } if ridx == comment_y::R_EXPR => {
                let mut s = String::new();
                for node in nodes {
                    s.push_str(&self.eval(node));
                }
                s
            }
            Node::Nonterm {
                ridx: RIdx(ridx),
                ref nodes,
            } if ridx == comment_y::R_TEXT => {
                if nodes.len() == 1 {
                    if let Node::Term { lexeme } = nodes[0] {
                        self.s[lexeme.span().start()..lexeme.span().end()].to_string()
                    } else {
                        unreachable!();
                    }
                } else {
                    let mut s = String::new();
                    for node in nodes {
                        s.push_str(&self.eval(node));
                    }
                    s
                }
            }
            _ => unreachable!(),
        }
    }
}
