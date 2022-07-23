# Parsing C-style block comments

This directory contains a very simple example of (non-nested) comment removal in `lrpar` that
uses the generic parse tree output of `lrpar`. `cargo build` processes
`src/comment.l` and `src/comment.y` at compile-time. The compiled program then takes
input from stdin. You can type anything in here (though you'll only get useful
output for valid input!) -- parsing and lexing errors are reported.

Look at `build.rs`, `src/comment.l`, `src/comment.y`, and `src/main.rs` to see how to use `lrpar`
in your project.
