// Copyright (c) 2018 King's College London
// created by the Software Development Team <http://soft-dev.org/>
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0>, or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, or the UPL-1.0 license <http://opensource.org/licenses/UPL>
// at your option. This file may not be copied, modified, or distributed except according to those
// terms.

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
                let mut lexer = lexerdef.lexer(l);
                match lexer.all_lexemes() {
                    Ok(lexemes) => println!("{:?}", lexemes),
                    Err(e) => println!("{:?}", e)
                }
            }
            _ => break
        }
    }
}
