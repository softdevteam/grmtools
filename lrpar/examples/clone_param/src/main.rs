#![allow(clippy::unnecessary_wraps)]

use lrlex::lrlex_mod;
use lrpar::lrpar_mod;
use std::io::{self, BufRead, Write};
use std::{cell::RefCell, rc::Rc};

// Using `lrlex_mod!` brings the lexer for `param.l` into scope. By default the module name will be
// `param_l` (i.e. the file name, minus any extensions, with a suffix of `_l`).
lrlex_mod!("param.l");
// Using `lrpar_mod!` brings the parser for `param.y` into scope. By default the module name will be
// `param_y` (i.e. the file name, minus any extensions, with a suffix of `_y`).
lrpar_mod!("param.y");

fn main() {
    // Get the `LexerDef` for the `param` language.
    let lexerdef = param_l::lexerdef();
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
                let param = Rc::new(RefCell::new(0));
                // Pass the lexer to the parser and lex and parse the input.
                let (_opt, errs) = param_y::parse(&lexer, param.clone());
                for e in errs {
                    println!("{}", e.pp(&lexer, &param_y::token_epp));
                }
                println!("Evaluated: {:?}", &param);
            }
            _ => break,
        }
    }
}
