# Grammar and parsing libraries for Rust

[![Build Status](https://api.travis-ci.org/softdevteam/sparsevec.svg?branch=master)](https://travis-ci.org/softdevteam/sparsevec)

This repository contains four Rust libraries for operating on Context-Free
Grammars (CFGs) and parsing. Although they make use of each other, each library
can be used individually. The libraries are neither complete nor stable, but
they may still be useful in their current form.

  * `cfgrammar`: a library for dealing with CFGs. Currently only supports
    grammars in Yacc format, though support for other formats may follow in the
    future.

  * `lrlex`: a basic lexer. It takes input files in a format similar, but
    deliberately not identical, to `lex` and produces a simple lexer. Can be
    used at compile-time (i.e. to produce `.rs` files, in similar fashion to
    `lex`), or at run-time (i.e. dynamically loading grammars without producing
    `.rs` files).

  * `lrpar`: a parser for LR grammars. Takes Yacc files and produces a parser
    that can produce a parse tree. Can be used at compile-time (i.e. to produce
    `.rs` files, in similar fashion to `yacc`), or at run-time (i.e. dynamically
    loading grammars without producing `.rs` files).

  * `lrtable`: a library for producing LR parse tables from grammars. Mostly
    of interest to those who wish to write their own LR parsing frameworks.

Since the APIs herein are somewhat unstable, you are encouraged to use the
specific git hash you relied on with the `rev` key when specifying dependencies
in your `Cargo.toml` file e.g.:

```
[build-dependencies]
lrpar = { git="https://github.com/softdevteam/grmtools/", rev="12345678" }
```


## nimbleparse

`nimbleparse` is a simple binary for dynamically testing lex files, grammars,
and inputs (which, internally, uses the above libraries). Use it as follows:

```sh
cargo run --release --bin nimbleparse <lex.l> <grm.y> <input file>
```

`nimbleparse` produces a parse tree as output and, if errors were encountered,
the repair sequences found.

## Documentation

Please refer to the [grmtools book](https://softdevteam.github.io/grmtools) for
a guide on how to get started.
