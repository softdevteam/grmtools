# Lexing a simple calculator language

This directory contains a very simple example of a calculator in `lrlex`.
Executing `cargo run` processes `src/calc.l` at compile-time; the resulting
binary then takes input from stdin. Each line should be a sequence of calculator
lexemes (note that, since this is a lexer example, there is no notion of lexeme
ordering: i.e. `1 2 +` is a valid sequence of lexemes as is `1
+ 2`).

Look at `build.rs`, `src/calc.l`, and `src/main.rs` to see how to use `lrlex` in
your project.
