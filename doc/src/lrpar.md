# `lrpar`

`lrpar` ([crate](https://crates.io/crates/lrpar);
[source](https://github.com/softdevteam/grmtools/tree/master/lrpar)) is the LR
parser library aspect of grmtools. It takes in streams of lexemes (using a
lexer of the user's choice) and parses them, determining if they successfully
match a grammar or not; if not, it can optionally recover from errors.
