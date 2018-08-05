use std::io::{self, BufRead, Write};

#[macro_use] extern crate lrlex;
#[macro_use] extern crate lrpar;

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
                // Note that each lexer can only lex one input in its lifetime.
                let lexer = lexerdef.lexer(l);
                match lexer.lexemes() {
                    Ok(lexemes) => {
                        // Now parse the stream of lexemes into a tree
                        match calc_y::parse(&lexemes) {
                            Ok(pt) => println!("{:?}", pt),
                            Err((_, errs)) => {
                                // One or more errors were detected during parsing.
                                for e in errs {
                                    let (line, col) = lexer.line_and_col(e.lexeme()).unwrap();
                                    assert_eq!(line, 1);
                                    println!("Error at column {}.", col);
                                }
                            }
                        }
                    },
                    Err(e) => println!("Lexing error {:?}", e)
                }
            },
            _ => break
        }
    }
}
