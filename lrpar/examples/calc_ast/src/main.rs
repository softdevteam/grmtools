use std::io::{self, BufRead, Write};

use lrlex::lrlex_mod;
use lrpar::{lrpar_mod, NonStreamingLexer, Span};

// Using `lrlex_mod!` brings the lexer for `calc.l` into scope. By default the module name will be
// `calc_l` (i.e. the file name, minus any extensions, with a suffix of `_l`).
lrlex_mod!("calc.l");
// Using `lrpar_mod!` brings the parser for `calc.y` into scope. By default the module name will be
// `calc_y` (i.e. the file name, minus any extensions, with a suffix of `_y`).
lrpar_mod!("calc.y");

use calc_y::Expr;

fn main() {
    // Get the `LexerDef` for the `calc` language.
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
                let lexer = lexerdef.lexer(l);
                // Pass the lexer to the parser and lex and parse the input.
                let (res, errs) = calc_y::parse(&lexer);
                for e in errs {
                    println!("{}", e.pp(&lexer, &calc_y::token_epp));
                }
                if let Some(Ok(r)) = res {
                    match eval(&lexer, r) {
                        Ok(i) => println!("Result: {}", i),
                        Err((span, msg)) => {
                            let ((line, col), _) = lexer.line_col(span);
                            eprintln!(
                                "Evaluation error at line {} column {}, '{}' {}.",
                                line,
                                col,
                                lexer.span_str(span),
                                msg
                            )
                        }
                    }
                }
            }
            _ => break,
        }
    }
}

fn eval(lexer: &dyn NonStreamingLexer<u32>, e: Expr) -> Result<u64, (Span, &'static str)> {
    match e {
        Expr::Add { span, lhs, rhs } => eval(lexer, *lhs)?
            .checked_add(eval(lexer, *rhs)?)
            .ok_or((span, "overflowed")),
        Expr::Mul { span, lhs, rhs } => eval(lexer, *lhs)?
            .checked_mul(eval(lexer, *rhs)?)
            .ok_or((span, "overflowed")),
        Expr::Number { span } => lexer
            .span_str(span)
            .parse::<u64>()
            .map_err(|_| (span, "cannot be represented as a u64")),
    }
}
