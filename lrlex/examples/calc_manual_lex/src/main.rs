#![allow(clippy::unnecessary_wraps)]

use std::io::{self, BufRead, Write};

use lrlex::{lrlex_mod, DefaultLexeme, LRNonStreamingLexer};
use lrpar::{lrpar_mod, Lexeme, NonStreamingLexer, Span};

lrlex_mod!("token_map");
// Using `lrpar_mod!` brings the parser for `calc.y` into scope. By default the module name will be
// `calc_y` (i.e. the file name, minus any extensions, with a suffix of `_y`).
lrpar_mod!("calc.y");

use calc_y::Expr;
use token_map::*;

fn main() {
    let stdin = io::stdin();
    loop {
        print!(">>> ");
        io::stdout().flush().ok();
        match stdin.lock().lines().next() {
            Some(Ok(ref l)) => {
                if l.trim().is_empty() {
                    continue;
                }
                let lexer = lex(l);
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

fn lex(s: &str) -> LRNonStreamingLexer<DefaultLexeme<u8>, u8> {
    let mut lexemes = Vec::new();
    let mut i = 0;
    while i < s.len() {
        // Skip whitespace
        i += s[i..]
            .chars()
            .take_while(|c| c.is_whitespace())
            .map(|c| c.len_utf8())
            .sum::<usize>();
        if i == s.len() {
            break;
        }
        match s[i..].chars().next().unwrap() {
            '+' => {
                lexemes.push(Ok(DefaultLexeme::new(T_PLUS, i, 1)));
                i += 1;
            }
            '*' => {
                lexemes.push(Ok(DefaultLexeme::new(T_STAR, i, 1)));
                i += 1;
            }
            '(' => {
                lexemes.push(Ok(DefaultLexeme::new(T_LBRACK, i, 1)));
                i += 1;
            }
            ')' => {
                lexemes.push(Ok(DefaultLexeme::new(T_RBRACK, i, 1)));
                i += 1;
            }
            _ => {
                let old_i = i;
                while let Some('0' | '1' | '2' | '3' | '4' | '5' | '6' | '7' | '8' | '9') =
                    s[i..].chars().next()
                {
                    i += 1;
                }
                if i > old_i {
                    lexemes.push(Ok(DefaultLexeme::new(T_INT, old_i, i - old_i)));
                } else {
                    let c_len = s[i..].chars().next().unwrap().len_utf8();
                    lexemes.push(Ok(DefaultLexeme::new(T_UNMATCHED, i, c_len)));
                    i += c_len;
                }
            }
        }
    }
    LRNonStreamingLexer::new(s, lexemes, Vec::new())
}

fn eval(
    lexer: &dyn NonStreamingLexer<DefaultLexeme<u8>, u8>,
    e: Expr,
) -> Result<u64, (Span, &'static str)> {
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
