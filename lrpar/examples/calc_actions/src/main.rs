use std::io::{self, BufRead, Write};

extern crate cfgrammar;
#[macro_use]
extern crate lrlex;
#[macro_use]
extern crate lrpar;

use lrpar::{LexParseError, Lexer};

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
                    // Success! We parsed the input and evaluated a result.
                    Ok(Ok(v)) => println!("Result: {}", v),
                    Ok(Err(_)) => eprintln!("Unable to evaluate a result."),
                    // We weren't able to fully lex the input, so all we can do is tell the user
                    // at what index the lexer gave up at.
                    Err(LexParseError::LexError(e)) => {
                        eprintln!("Lexing error at column {:?}", e.idx)
                    }
                    // Parsing failed, but with the help of error recovery a value was
                    // produced.
                    Err(LexParseError::ParseError(v, errs)) => {
                        // One or more errors were detected during parsing.
                        for e in errs {
                            let (line, col) = lexer.line_and_col(e.lexeme());
                            assert_eq!(line, 1);
                            eprintln!("Parsing error at column {}.", col);
                        }
                        match v {
                            Some(Ok(v)) => println!("Result: {}", v),
                            _ => eprintln!("Unable to evaluate a result.")
                        }
                    }
                }
            }
            _ => break
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use lrpar::LexParseError;

    #[test]
    fn test_basic_actions() {
        let lexerdef = calc_l::lexerdef();
        let mut lexer = lexerdef.lexer("2+3");
        match calc_y::parse(&mut lexer) {
            Ok(Ok(5)) => (),
            _ => unreachable!()
        }
    }

    #[test]
    fn test_error_recovery_and_actions() {
        let lexerdef = calc_l::lexerdef();
        let mut lexer = lexerdef.lexer("2++3");
        match calc_y::parse(&mut lexer) {
            Err(LexParseError::ParseError(Some(Ok(5)), ..)) => (),
            _ => unreachable!()
        }
        let mut lexer = lexerdef.lexer("2+3)");
        match calc_y::parse(&mut lexer) {
            Err(LexParseError::ParseError(Some(Ok(5)), ..)) => (),
            _ => unreachable!()
        }
        let mut lexer = lexerdef.lexer("2+3+18446744073709551616");
        match calc_y::parse(&mut lexer) {
            Ok(Err(_)) => (),
            _ => unreachable!()
        }
    }
}
