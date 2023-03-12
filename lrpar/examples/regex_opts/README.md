# Configuring the behavior of the regex engine.

This directory contains a very simple example of configuring the underlying
regex engine to modify it's behavior with respect to whether the `.` regex
includes newlines or not.

Look at `build.rs`, `src/any.l`, and `src/main.rs` to see how to use `lrpar` in
your project.
