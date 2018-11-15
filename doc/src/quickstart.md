# Quickstart Guide

This is a short guide to get you started with lrpar and shows how to generate a
standalone parser from a given grammar. lrpar is meant to be used as a
replacement for the parser generator
[Yacc](https://en.wikipedia.org/wiki/Yacc), and thus uses the same syntax
wherever possible. The main difference is the grammar actions which, unlike
Yacc, need to be written in Rust. Similar to Yacc, we need to define both
lexing and parsing rules. The lexing rules are used to tokenise the user input
which are then handed over to the parser. The parser then generates a parse
tree according to the parsing rules, or alternatively executes the grammar
actions. In this example we will use lrlex to define our lexing rules as
regular expressions. However, the lexer is completely interchangeable and can
be replaced with a more sophisticated version if needed. For more information
and detailed explanations please refer to the [tutorial](tutorial/index.html).

We begin by creating a `Cargo.toml` file and specifying the necessary dependencies:

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

In the root of the project we create a file `build.rs`, which processes our
lexer and grammar files. Here we can choose whether we want to generate a
default parse tree, or use grammar actions instead:

```rust
extern crate lrlex;
extern crate lrpar;

use lrlex::LexerBuilder;
use lrpar::{CTParserBuilder, ActionKind};

fn main() -> Result<(), Box<std::error::Error>> {
    let lex_rule_ids_map = CTParserBuilder::new().action_kind(ActionKind::CustomAction).process_file_in_src("calc.y")?;
    LexerBuilder::new()
        .rule_ids_map(lex_rule_ids_map)
        .process_file_in_src("calc.l")?;
    Ok(())
}
```

In this example we are using `CustomAction` to write a simple calculator
grammar that calculates user input as it is being parsed. We define lexing and
grammar rules as follows, and store them in `calc.l` and `calc.y` respectively:

calc.l:
```
%%
[0-9]+ "INT"
\+ "PLUS"
\* "MUL"
\( "LBRACK"
\) "RBRACK"
[\t ]+ ;
```

calc.y:
```
%start Expr
// Define the type that is to be returned by the actions. Can also be an enum.
%type MYTYPE
%%
Expr: Term 'PLUS' Expr { add($1, $3) }
    | Term { $1 }
    ;

Term: Factor 'MUL' Term { mul ($1, $3) }
    | Factor { $1 }
    ;

Factor: 'LBRACK' Expr 'RBRACK' { $2 }
      | 'INT' { int($1) }
      ;
%%

type MYTYPE = u64;

// The following functions are in scope for all the grammar actions above.

fn int(s: &str) -> MYTYPE {
    match s.parse::<u64>() {
    	Ok(val) => val as MYTYPE,
	Err(_) => unreachable!()
    }
}

fn add(arg1: u64, arg2: u64) -> u64 {
    arg1 + arg2
}

fn mul(arg1: u64, arg2: u64) -> u64 {
    arg1 * arg2
}
```

Now we can create the main function for our program which uses the parser
generated in `build.rs`. When run, this program will take some user input,
parse it according to the grammar, and return the result of the grammar
actions:

```rust
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
                    // Success! We parsed the input.
                    Ok(pt) => println!("Result: {}", pt),
                    // We weren't able to fully lex the input, so all we can do is tell the user
                    // at what index the lexer gave up at.
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
