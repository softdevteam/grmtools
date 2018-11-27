# Parsing a simple calculator language

This directory contains a very simple example of a calculator in `lrpar` that
uses the generic parse tree output of `lrpar`. `cargo build` processes
`src/calc.l` and `src/calc.y` at compile-time. The compiled program then takes
input from stdin. You can type anything in here (though you'll only get useful
output for valid input!) -- parsing and lexing errors are reported.

Look at `build.rs`, `src/calc.y`, and `src/main.rs` to see how to use `lrpar` in
your project.
