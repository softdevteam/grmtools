# Action code and return types

## Action code

Action code is normal Rust code with the addition of the following special variables:

 * `$1` ... `$n` refer to the respective symbol in the production, numbered
   from 1 (i.e. `$1` refers to the first symbol in the production). If the
   symbol references a rule `R` then an instance of `R`'s type will be stored
   in the `$i` variable; if the symbol references a lexeme then an
   `Option<Lexeme>` instance is returned.

 * `$lexer` allows access to the lexer and its [various
   functions](https://softdevteam.github.io/grmtools/master/api/lrpar/trait.Lexer.html).
   The most commonly used of these is the `span_str` function, which allows us
   to extract `&'input str`s from a `Span` (e.g. to extract the string
   represented by a `Lexeme`, we would use `$lexer.span_str(lexeme.span())`).
   As this may suggest, actions may also reference the special lifetime
   `'input` (without any `$` prefix), which allows strings to be returned /
   stored by the grammar without copying memory.

 * `$span` is a
   [`lrpar::Span`](https://softdevteam.github.io/grmtools/master/api/lrpar/struct.Span.html)
   tuple (with both elements of type `usize`) which captures how much of the
   user's input the current production matched.

 * `$$` is equivalent to `$` in normal Rust code.

Any other variables beginning with `$` are treated as errors.


## Return types

Productions' return types can be any arbitrary Rust type. You may in addition
make use of the following:

 * The generic parameter `StorageT` references the type of lexemes and is
   typically used with the
   [`Lexeme`](https://softdevteam.github.io/grmtools/master/api/lrpar/struct.Lexeme.html)
   type i.e. `Lexeme<StorageT>`. This allows you to return lexemes from rules.

 * The lifetime `'input` allows you to extract strings whose lifetime is tied
   to the lexer and return them from rules / store them in structs without
   copying. `Lexer::span_str` returns such strings and the typical idiom of use
   is `&'input str`.
