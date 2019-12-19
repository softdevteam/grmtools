# Grammar and parsing libraries for Rust

[![Build Status](https://api.travis-ci.org/softdevteam/sparsevec.svg?branch=master)](https://travis-ci.org/softdevteam/sparsevec)

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
use lrpar::{CTParserBuilder};

fn main() -> Result<(), Box<std::error::Error>> {
    let lex_rule_ids_map = CTParserBuilder::new()
        .yacckind(YaccKind::Grmtools)
        .process_file_in_src("grammar.y")?;
    LexerBuilder::new()
        .rule_ids_map(lex_rule_ids_map)
        .process_file_in_src("lexer.l")?;
    Ok(())
}
```

This will generate and compile a parser and lexer using the definitions found
in `src/lexer.l` and `src/grammar.y`. We can then use the generated lexer and
parser within our `src/main.rs` file as follows:

```rust
use std::env;

use lrlex::lrlex_mod;
use lrpar::lrpar_mod;

// Using `lrlex_mod!` brings the lexer for `calc.l` into scope.
lrlex_mod!(calc_l);
// Using `lrpar_mod!` brings the parser for `calc.y` into scope.
lrpar_mod!(calc_y);

fn main() {
    // We need to get a `LexerDef` for the `calc` language in order that we can
    // lex input.
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
