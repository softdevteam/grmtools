# Action code

Action code is normal Rust code with the addition of the following special variables:

 * `$1` ... `$n` refer to the respective symbol in the production, numbered
   from 1 (i.e. `$1` refers to the first symbol in the production). If the
   symbol references a rule `R` then an instance of `R`'s type will be stored
   in the `$i` variable; if the symbol references a lexeme then an
   `Option<Lexeme>` instance is returned.

 * `$lexer` allows access to the lexer and its [various
   functions](https://softdevteam.github.io/grmtools/master/api/lrpar/trait.Lexer.html).
   The most commonly used of these is the `lexeme_str` function, which allows
   us to turn `Lexeme`s into `&str`s representing the corresponding portion of
   the user's input.

 * `$span` is a `(start, end)` tuple (with both elements of type `usize`) which
   captures how much of the user's input the current production matched. This
   can be useful when storing debugging information. Note that this variable is
   not enabled by default: use `CTParserBuilder::span_var(true)` to enable it.

 * `$$` is equivalent to `$` in normal Rust code.

Any other variables beginning with `$` are treated as errors.
