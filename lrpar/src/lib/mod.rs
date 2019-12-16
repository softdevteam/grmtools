#![allow(clippy::cognitive_complexity)]
#![allow(clippy::many_single_char_names)]
#![allow(clippy::needless_doctest_main)]
#![allow(clippy::new_without_default)]
#![allow(clippy::range_plus_one)]
#![allow(clippy::too_many_arguments)]
#![allow(clippy::type_complexity)]

//! `lrpar` provides a Yacc-compatible parser (where grammars can be generated at
//! compile-time or run-time). It can take in traditional `.y` files and convert
//! them into an idiomatic Rust parser. More details can be found in the [grmtools
//! book](https://softdevteam.github.io/grmtools/master/book); the
//! [quickstart guide](https://softdevteam.github.io/grmtools/master/book/quickstart.html)
//! is a good place to start.
//!
//!
//! ## Example
//!
//! Let's assume we want to statically generate a parser for a simple calculator
//! language (and let's also assume we are able to use
//! [`lrlex`](https://softdevteam.github.io/grmtools/master/book/lrlex.html) for the
//! lexer). We need to add a `build.rs` file to our project which tells `lrpar` to
//! statically compile the lexer and parser files:
//!
//! ```text
//! use cfgrammar::yacc::YaccKind;
//! use lrlex::LexerBuilder;
//! use lrpar::CTParserBuilder;
//!
//! fn main() -> Result<(), Box<dyn std::error::Error>> {
//!     let lex_rule_ids_map = CTParserBuilder::new()
//!         .yacckind(YaccKind::Grmtools)
//!         .process_file_in_src("calc.y")?;
//!     LexerBuilder::new()
//!         .rule_ids_map(lex_rule_ids_map)
//!         .process_file_in_src("calc.l")?;
//!     Ok(())
//! }
//! ```
//!
//! where `src/calc.l` is as follows:
//!
//! ```text
//! %%
//! [0-9]+ "INT"
//! \+ "+"
//! \* "*"
//! \( "("
//! \) ")"
//! [\t ]+ ;
//! ```
//!
//! and `src/calc.y` is as follows:
//!
//! ```text
//! %start Expr
//! %avoid_insert "INT"
//! %%
//! Expr -> Result<u64, ()>:
//!       Term '+' Expr { Ok($1? + $3?) }
//!     | Term { $1 }
//!     ;
//!
//! Term -> Result<u64, ()>:
//!       Factor '*' Term { Ok($1? * $3?) }
//!     | Factor { $1 }
//!     ;
//!
//! Factor -> Result<u64, ()>:
//!       '(' Expr ')' { $2 }
//!     | 'INT'
//!       {
//!           let v = $1.map_err(|_| ())?;
//!           parse_int($lexer.lexeme_str(&v))
//!       }
//!     ;
//! %%
//! // Any functions here are in scope for all the grammar actions above.
//!
//! fn parse_int(s: &str) -> Result<u64, ()> {
//!     match s.parse::<u64>() {
//!         Ok(val) => Ok(val),
//!         Err(_) => {
//!             eprintln!("{} cannot be represented as a u64", s);
//!             Err(())
//!         }
//!     }
//! }
//! ```
//!
//! Because we specified that our Yacc file is in `Grmtools` format, each rule has a
//! separate Rust type to which all its functions conform (in this case, all the
//! rules have the same type, but that's not a requirement).
//!
//! A simple `src/main.rs` is as follows:
//!
//! ```text
//! use std::io::{self, BufRead, Write};
//!
//! use lrlex::lrlex_mod;
//! use lrpar::lrpar_mod;
//!
//! // Using `lrlex_mod!` brings the lexer for `calc.l` into scope.
//! lrlex_mod!(calc_l);
//! // Using `lrpar_mod!` brings the lexer for `calc.l` into scope.
//! lrpar_mod!(calc_y);
//!
//! fn main() {
//!     // We need to get a `LexerDef` for the `calc` language in order that we can lex input.
//!     let lexerdef = calc_l::lexerdef();
//!     let stdin = io::stdin();
//!     loop {
//!         print!(">>> ");
//!         io::stdout().flush().ok();
//!         match stdin.lock().lines().next() {
//!             Some(Ok(ref l)) => {
//!                 if l.trim().is_empty() {
//!                     continue;
//!                 }
//!                 // Now we create a lexer with the `lexer` method with which we can lex an input.
//!                 let mut lexer = lexerdef.lexer(l);
//!                 // Pass the lexer to the parser and lex and parse the input.
//!                 let (res, errs) = calc_y::parse(&mut lexer);
//!                 for e in errs {
//!                     println!("{}", e.pp(&lexer, &calc_y::token_epp));
//!                 }
//!                 match res {
//!                     Some(Ok(r)) => println!("Result: {}", r),
//!                     _ => eprintln!("Unable to evaluate expression.")
//!                 }
//!             }
//!             _ => break
//!         }
//!     }
//! }
//! ```
//!
//! We can now `cargo run` our project and evaluate simple expressions:
//!
//! ```text
//! >>> 2 + 3
//! Result: 5
//! >>> 2 + 3 * 4
//! Result: 14
//! >>> (2 + 3) * 4
//! Result: 20
//! ```
//!
//! `lrpar` also comes with advanced [error
//! recovery](https://softdevteam.github.io/grmtools/master/book/errorrecovery.html) built-in:
//!
//! ```text
//! >>> 2 + + 3
//! Parsing error at line 1 column 5. Repair sequences found:
//!    1: Delete +
//!    2: Insert INT
//! Result: 5
//! >>> 2 + 3 3
//! Parsing error at line 1 column 7. Repair sequences found:
//!    1: Insert *
//!    2: Insert +
//!    3: Delete 3
//! Result: 11
//! >>> 2 + 3 4 5
//! Parsing error at line 1 column 7. Repair sequences found:
//!    1: Insert *, Delete 4
//!    2: Insert +, Delete 4
//!    3: Delete 4, Delete 5
//!    4: Insert +, Shift 4, Delete 5
//!    5: Insert +, Shift 4, Insert +
//!    6: Insert *, Shift 4, Delete 5
//!    7: Insert *, Shift 4, Insert *
//!    8: Insert *, Shift 4, Insert +
//!    9: Insert +, Shift 4, Insert *
//! Result: 17
//! ```

mod astar;
mod cpctplus;
#[doc(hidden)]
pub mod ctbuilder;
#[doc(hidden)]
pub mod lex;
pub use crate::lex::{LexError, Lexeme, Lexer};
mod panic;
#[doc(hidden)]
pub mod parser;
pub use crate::{
    ctbuilder::CTParserBuilder,
    parser::{LexParseError, Node, ParseError, ParseRepair, RTParserBuilder, RecoveryKind}
};
mod mf;

/// A convenience macro for including statically compiled `.y` files. A file `src/a/b/c.y` which is
/// statically compiled by lrpar can then be used in a crate with `lrpar_mod!("a/b/c.y")`.
#[macro_export]
macro_rules! lrpar_mod {
    ($path:expr) => {
        include!(concat!(env!("OUT_DIR"), "/", $path, ".rs"));
    };
}

#[doc(hidden)]
pub use cfgrammar::RIdx;
