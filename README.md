# Grammar and parsing libraries for Rust

[![Bors enabled](https://bors.tech/images/badge_small.svg)](https://app.bors.tech/repositories/22484) [![lrpar on crates.io](https://img.shields.io/crates/v/lrpar.svg?label=lrpar)](https://crates.io/crates/lrpar) [![lrlex on crates.io](https://img.shields.io/crates/v/lrlex.svg?label=lrlex)](https://crates.io/crates/lrlex) [![lrtable on crates.io](https://img.shields.io/crates/v/lrtable.svg?label=lrtable)](https://crates.io/crates/lrtable) [![cfgrammar on crates.io](https://img.shields.io/crates/v/cfgrammar.svg?label=cfgrammar)](https://crates.io/crates/cfgrammar)

grmtools is a suite of Rust libraries and binaries for parsing text, both at
compile-time, and run-time. Most users will probably be interested in the
compile-time Yacc feature, which allows traditional `.y` files to be used
(mostly) unchanged in Rust.

## Quickstart

A minimal example using this library consists of two files (in addition to the
grammar and lexing definitions). First we need to create a file `build.rs` in
the root of our project with the following content:

```rust
use cfgrammar::yacc::YaccKind;
use lrlex::LexerBuilder;
use lrpar::CTParserBuilder;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let lex_rule_ids_map = CTParserBuilder::new()
        .yacckind(YaccKind::Grmtools)
        .grammar_in_src_dir("grammar.y")?
        .process();
    LexerBuilder::new()
        .rule_ids_map(lex_rule_ids_map)
        .lexer_in_src_dir("lexer.l")?
        .process();
    Ok(())
}
```

This will generate and compile a parser and lexer, where the definitions for the
lexer can be found in `src/calc.l`:

```rust
%%
[0-9]+ "INT"
\+ "+"
\* "*"
\( "("
\) ")"
[\t ]+ ;
```

And where the definitions for the parser can be found in `src/calc.y`:

```rust
%start Expr
%avoid_insert "INT"
%%
Expr -> Result<u64, ()>:
      Expr '+' Term { Ok($1? + $3?) }
    | Term { $1 }
    ;

Term -> Result<u64, ()>:
      Term '*' Factor { Ok($1? * $3?) }
    | Factor { $1 }
    ;

Factor -> Result<u64, ()>:
      '(' Expr ')' { $2 }
    | 'INT'
      {
          let v = $1.map_err(|_| ())?;
          parse_int($lexer.span_str(v.span()))
      }
    ;
%%
// Any functions here are in scope for all the grammar actions above.

fn parse_int(s: &str) -> Result<u64, ()> {
    match s.parse::<u64>() {
        Ok(val) => Ok(val),
        Err(_) => {
            eprintln!("{} cannot be represented as a u64", s);
            Err(())
        }
    }
}
```

We can then use the generated lexer and parser within our `src/main.rs` file as
follows:

```rust
use std::env;

use lrlex::lrlex_mod;
use lrpar::lrpar_mod;

// Using `lrlex_mod!` brings the lexer for `calc.l` into scope. By default the
// module name will be `calc_l` (i.e. the file name, minus any extensions,
// with a suffix of `_l`).
lrlex_mod!("calc.l");
// Using `lrpar_mod!` brings the parser for `calc.y` into scope. By default the
// module name will be `calc_y` (i.e. the file name, minus any extensions,
// with a suffix of `_y`).
lrpar_mod!("calc.y");

fn main() {
    // Get the `LexerDef` for the `calc` language.
    let lexerdef = calc_l::lexerdef();
    let args: Vec<String> = env::args().collect();
    // Now we create a lexer with the `lexer` method with which we can lex an
    // input.
    let lexer = lexerdef.lexer(&args[1]);
    // Pass the lexer to the parser and lex and parse the input.
    let (res, errs) = calc_y::parse(&lexer);
    for e in errs {
        println!("{}", e.pp(&lexer, &calc_y::token_epp));
    }
    match res {
        Some(r) => println!("Result: {:?}", r),
        _ => eprintln!("Unable to evaluate expression.")
    }
}
```

For more information on how to use this library please refer to the [grmtools
book](https://softdevteam.github.io/grmtools/master/book/), which also includes
a more detailed [quickstart
guide](https://softdevteam.github.io/grmtools/master/book/quickstart.html).

## Examples

[lrpar](https://github.com/softdevteam/grmtools/tree/master/lrpar/examples)
contains several examples on how to use the `lrpar`/`lrlex` libraries, showing
how to generate [parse
trees](https://github.com/softdevteam/grmtools/tree/master/lrpar/examples/calc_parsetree)
and
[ASTs](https://github.com/softdevteam/grmtools/tree/master/lrpar/examples/calc_ast),
or [execute
code](https://github.com/softdevteam/grmtools/tree/master/lrpar/examples/calc_actions)
while parsing.

## Documentation

- [grmtools book](https://softdevteam.github.io/grmtools/master/book/)
- [lrpar](https://docs.rs/lrpar/)
- [lrlex](https://docs.rs/lrlex/)
- [lrtable](https://docs.rs/lrtable/)
