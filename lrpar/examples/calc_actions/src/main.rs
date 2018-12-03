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
                let (res, errs) = calc_y::parse(&mut lexer);
                for e in errs {
                    match e {
                        LexParseError::LexError(e) => {
                            eprintln!("Lexing error at column {:?}", e.idx)
                        }
                        LexParseError::ParseError(e) => {
                            let (line, col) = lexer.line_and_col(e.lexeme());
                            assert_eq!(line, 1);
                            eprintln!("Parsing error at column {}", col);
                        }
                    }
                }
                match res {
                    Some(Ok(r)) => println!("Result: {}", r),
                    _ => eprintln!("Unable to evaluate expression.")
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
            (Some(Ok(5)), ref errs) if errs.len() == 0 => (),
            _ => unreachable!()
        }
    }

    #[test]
    fn test_error_recovery_and_actions() {
        let lexerdef = calc_l::lexerdef();

        let mut lexer = lexerdef.lexer("2++3");
        let (r, errs) = calc_y::parse(&mut lexer);
        assert_eq!(r, Some(Ok(5)));
        assert_eq!(errs.len(), 1);
        match errs[0] {
            LexParseError::ParseError(..) => (),
            _ => unreachable!()
        }

        let mut lexer = lexerdef.lexer("2+3)");
        let (r, errs) = calc_y::parse(&mut lexer);
        assert_eq!(r, Some(Ok(5)));
        assert_eq!(errs.len(), 1);
        match errs[0] {
            LexParseError::ParseError(..) => (),
            _ => unreachable!()
        }

        let mut lexer = lexerdef.lexer("2+3+18446744073709551616");
        let (r, errs) = calc_y::parse(&mut lexer);
        assert_eq!(r, Some(Err(())));
        assert!(errs.is_empty());
    }
}
