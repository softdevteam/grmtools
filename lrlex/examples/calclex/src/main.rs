use std::io::{self, BufRead, Write};

use lrlex::lrlex_mod;
use lrpar::Lexer;

// Using `lrlex_mod!` brings the lexer for `calc.l` into scope. By default the module name will be
// `calc_l` (i.e. the file name, minus any extensions, with a suffix of `_l`).
lrlex_mod!("calc.l");

fn main() {
    // Get the `LexerDef` for the `calc` language.
    let lexerdef = calc_l::lexerdef();
    let stdin = io::stdin();
    loop {
        print!(">>> ");
        io::stdout().flush().ok();
        match stdin.lock().lines().next() {
            Some(Ok(ref l)) => {
                // Now we create a lexer with the `lexer` method with which we can lex an input.
                // Note that each lexer can only lex one input in its lifetime.
                let lexer = lexerdef.lexer(l);
                println!("{:?}", lexer.iter().collect::<Vec<_>>());
            }
            _ => break,
        }
    }
}
