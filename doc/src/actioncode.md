# Action code and return types

## Action code

Action code is normal Rust code with the addition of the following special variables:

 * `$1` ... `$n` refer to the respective symbol in the production, numbered
   from 1 (i.e. `$1` refers to the first symbol in the production). If the
   symbol references a rule `R` then an instance of `R`'s type will be stored
   in the `$i` variable. If the symbol references a lexeme then a
   `Result<Lexeme<StorageT>, Lexeme<StorageT>>` instance is returned where the
   `Ok` variant is used for lexemes that are directly derived from the user's
   input and the `Err` variant is used for lexemes that have been inserted by
   [error recovery](errorrecovery.md).

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


## Additional parse parameter

A single extra parameter can be passed to action functions if the `%parse-param
<var>: <type>` declaration is used. The variable `<var>` is then visible in all
action code. Note that `<type>` must implement the [`Copy`
trait](https://doc.rust-lang.org/std/marker/trait.Copy.html). If you wish to
pass a reference it must currently be tied to the `'input` lifetime (i.e.
`%parse-param x: &'lifetime ...`).

For example if a grammar has a declaration:

```
%parse-param p: u64
```

then the statically generated `parse` function will take two paramaters
`(lexer: &..., p: u64)` and the variable `p` can be used in action code e.g.:

```
R -> ...:
  'ID' { format!("{}{}", p, ...) }
  ;
```
