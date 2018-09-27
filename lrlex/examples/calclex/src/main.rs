use std::io::{self, BufRead, Write};

#[macro_use]
extern crate lrlex;
extern crate lrpar;

use lrpar::Lexer;

// Using `lrlex_mod!` brings the lexer for `calc.l` into scope.
lrlex_mod!(calc_l);

fn main() {
    // We need to get a `LexerDef` for the `calc` language in order that we can lex input.
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
                match lexer.lexemes() {
                    Ok(lexemes) => println!("{:?}", lexemes),
                    Err(e) => println!("{:?}", e)
                }
            }
            _ => break
        }
    }
}
