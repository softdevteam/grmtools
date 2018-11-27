# Quickstart Guide

Most users will probably be interested in the compile-time Yacc feature of
grmtools, which allows traditional `.y` files to be used mostly unchanged in
Rust. This page is a short guide to get you up and running with this feature as
quickly as possible.

grmtools includes both a Yacc-style LR parser ([`lrpar`](lrpar.html)) and a
lex-style lexer ([`lrlex`](lrlex.html)). The lexer breaks input up into individual lexemes and
the parser checks to see if the lexemes conform to a grammar. As the parser
executes, it can either create a generic parse tree, or execute user-specified
Rust code.


## A calculator evaluator

Let's assume we want to create a simple calculator which can evaluate
expressions such as `2 + 3 * 4`. Assuming a fresh Rust project, we first create
a `Cargo.toml` file with the following dependencies:

```toml
[package]
name = "calc"
version = "0.0.1"
authors = ["<authors>"]

[[bin]]
doc = false
name = "calc"

[build-dependencies]
lrlex = { path="<path to lrlex>" }
lrpar = { path="<path to lrpar>" }

[dependencies]
cfgrammar = { path="<path to cfgrammar>" }
lrlex = { path="<path to lrlex>" }
lrpar = { path="<path to lrpar>" }
```

In this situation we want to statically compile the `.y` grammar and `.l` lexer
into Rust code. We thus need to create a
[`build.rs`](https://doc.rust-lang.org/cargo/reference/build-scripts.html)
file which can process the lexer and grammar.  Our `build.rs` file thus looks as follows:

```rust
extern crate lrlex;
extern crate lrpar;

use lrlex::LexerBuilder;
use lrpar::{CTParserBuilder, ActionKind};

fn main() -> Result<(), Box<std::error::Error>> {
    let lex_rule_ids_map = CTParserBuilder::new()
        .action_kind(ActionKind::CustomAction)
        .process_file_in_src("calc.y")?;
    LexerBuilder::new()
        .rule_ids_map(lex_rule_ids_map)
        .process_file_in_src("calc.l")?;
    Ok(())
}
```

In our case, we want to specify Rust code which is run as the input is parsed
(rather than creating a generic parse tree which we traverse later), so we
specified that the `action_kind` is `ActionKind::CustomAction`. The grammar file
is stored in `src/calc.y`, but we only specify `calc.y` as the filename to
`lrpar`, since it searches relative to `src/` automatically.


## The lexer

While Yacc-style parsing is powerful, lex-style lexing is less powerful.
grmtools allows you to use whatever lexer you want with `lrpar`. Fortunately, in
this case, `lrlex` is powerful enough for us. Our lex file is stored in
`src/calc.l`. The `rule_ids_map` dance synchronises the parser and lexer (the
details of this are unimportant to us).

`calc.l` is as follows:
```lex
%%
[0-9]+ "INT"
\+ "PLUS"
\* "MUL"
\( "LBRACK"
\) "RBRACK"
[\t ]+ ;
```

Roughly speaking, each line after the `%%` line is a regular expression (we use
the [`regex`](https://crates.io/crates/regex) crate), a space character, and a
quoted lexeme type name. For example, if the user gives us input such as `234`
we will create a single lexeme with a value (`234`) and a type (`INT`).

The one exception is the final line: if a lexeme type name is replaced with ‘`;`’
then any matching input is discarded. In this case, whitespace (tabs and spaces)
is lexed, but no lexemes are created from it.


## The grammar

calc.y is as follows:
```yacc
%start Expr
// Define the Rust type that is to be returned by the actions.
%type u64
%%
Expr: Term 'PLUS' Expr { $1 + $3 }
    | Term { $1 }
    ;

Term: Factor 'MUL' Term { $1 * $3 }
    | Factor { $1 }
    ;

Factor: 'LBRACK' Expr 'RBRACK' { $2 }
      | 'INT' { parse_int($1) }
      ;
%%
// Any functions here are in scope for all the grammar actions above.

fn parse_int(s: &str) -> u64 {
    match s.parse::<u64>() {
    	Ok(val) => val as u64,
        Err(_) => panic!("{} cannot be represented as a u64", s)
    }
}
```

The grammar is in 3 parts, separated by the `%%` lines.

The first part specifies general settings for the grammar: its start rule
(`Expr`) and the Rust type that actions in the grammar must produce (`u64`).

The second part is the [Yacc
grammar](http://dinosaur.compilertools.net/yacc/index.html). It consists of 3
rules (`Expr`, `Term`, and `Factor`) and 6 productions (2 for each rule,
separated by `|` characters). A production (sometimes called an “alternative”)
consists of zero or more symbols. Symbols either reference rules or lexemes. If a
production matches text, its ”action” (the Rust code between curly brackets at
the end of the production) is executed. `lrpar`'s actions are slightly different
to Yacc. The `$x` variables refer to the respective symbol in the production
(i.e. `$1` refers to the first symbol in the production). If the symbol is a
rule then an instance of the `%type` is stored in the `$x` variable; if the
symbol is a lexeme then a string is stored instead.

The third part is arbitrary Rust code which can be called by productions’
actions. In our case we have a simple function which converts integers as
strings into integers as `u64`s: if the user provides an invalid number (e.g.
one that is too big) an error will be printed.


## Putting everything together

The `build.rs` file will statically compile the lexer and grammar into Rust code
that we can then call. The below `src/main.rs` file provides a simple
Python-esque REPL to the user into which they can write calculator expressions:

```rust
extern crate lrpar;

use lrpar::{LexParseError, Lexer};

// Using `lrlex_mod!` brings the lexer for `calc.l` into scope.
lrlex_mod!(calc_l);
// Using `lrpar_mod!` brings the lexer for `calc.l` into scope.
lrpar_mod!(calc_y);

fn main() {
    // We need to get a `LexerDef` for the `calc` language in order that we can
    // lex input.
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
                // Now we create a lexer with the `lexer` method with which we
                // can lex an input.
                let mut lexer = lexerdef.lexer(l);
                // Pass the lexer to the parser and lex and parse the input.
                match calc_y::parse(&mut lexer) {
                    // Success! We parsed the input.
                    Ok(pt) => println!("Result: {}", pt),
                    // We weren't able to fully lex the input, so all we can do
                    // is tell the user at what index the lexer gave up at.
                    Err(LexParseError::LexError(e)) => {
                        println!("Lexing error at column {:?}", e.idx)
                    }
                    // Parsing failed, so we simply report the error to the user.
                    Err(LexParseError::ParseError(_, errs)) => {
                        // One or more errors were detected during parsing.
                        for e in errs {
                            let (line, col) = lexer.line_and_col(e.lexeme()).unwrap();
                            assert_eq!(line, 1);
                            println!("Parsing error at column {}.", col);
                        }
                    }
                }
            }
            _ => break
        }
    }
}
```


## What to do next

One of `lrpar`s unusual features is its advanced error recovery approach. With
some simple annotations, and a bit of work to present information to the user,
[high quality reports can be given to the user when they make syntactic
errors](errorrecovery.html).
