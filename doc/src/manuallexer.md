# Hand-written lexers

`lrpar` provides a generic lexing interface to which any lexer can plug into.
Users can provide
one or both of a custom lexeme type -- conforming to
[`lrpar::Lexeme`](https://softdevteam.github.io/grmtools/master/api/lrpar/trait.Lexeme.html)
-- and a custom lexing type -- conforming to
[`lrpar::NonStreamingLexer`](https://softdevteam.github.io/grmtools/master/api/lrpar/trait.NonStreamingLexer.html).
If you wish to use a custom lexer, you will need to instantiate `lrpar`
appropriately (both
[`CTParserBuilder`](https://softdevteam.github.io/grmtools/master/api/lrpar/struct.CTParserBuilder.html)
and
[`RTParserBuilder`](https://softdevteam.github.io/grmtools/master/api/lrpar/struct.RTParserBuilder.html)).

For many purposes, the low-level control and performance that `lrpar` gives you is unneeded,
and the boiler-plate that comes with it unwanted. Fortunately, `lrlex` provides the following convenience mechanisms to make it easier to use a hand-written lexer with `lrpar`:

  1. `lrlex`'s normal `LRNonStreamingLexer` struct can be instantiated by an
      end-user with an input stream, a list of lexemes created from that
      input stream, and the newlines encountered while lexing that input
      stream. This saves having to define a custom instance of the
      [`lrpar::NonStreamingLexer`](https://softdevteam.github.io/grmtools/master/api/lrpar/trait.NonStreamingLexer.html)
      trait.

  2. `lrlex`'s [`DefaultLexeme`](https://softdevteam.github.io/grmtools/master/api/lrlex/struct.DefaultLexeme.html)
     struct can also be instantiated by end-users, saving having to define a
     custom instance of the
     [`lrpar::Lexeme`](https://softdevteam.github.io/grmtools/master/api/lrpar/trait.Lexeme.html)
     trait.

  3. `lrlex` exposes a
     [`ct_token_map`](https://softdevteam.github.io/grmtools/master/api/lrlex/fn.ct_token_map.html)
     function to be used from `build.rs` scripts which automatically produces a
     Rust module with one constant per token ID. `ct_token_map` is explicitly
     designed to be easy to use with `lrpar`'s compile-time building.

Putting these together is then relatively easy. First a `build.rs` file for a
hand-written lexer will look roughly as follows:

```rust
use cfgrammar::yacc::YaccKind;
use lrlex::{ct_token_map, DefaultLexeme};
use lrpar::CTParserBuilder;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let ctp = CTParserBuilder::<DefaultLexeme<u8>, u8>::new()
        .yacckind(YaccKind::Grmtools)
        .grammar_in_src_dir("grammar.y")?
        .build()?;
    ct_token_map::<u8>("token_map", ctp.token_map(), None)
}
```

This produces a module that can be imported with `lrlex_mod!("token_map")`. The
module will contain one constant, prefixed with `T_` per token identifiers in the
grammar. For example, for the following grammar excerpt:

```lex
Expr -> Result<u64, ()>:
      Expr 'PLUS' Term { Ok($1? + $3?) }
    | Term { $1 }
    ;
```

the module will contain `const T_PLUS: u8 = ...;`.

Since Yacc grammars can contain token identifiers which are not valid Rust
identifiers, `ct_token_map` allows you to provide a map from the token
identifier to a "Rust friendly" variant. For example, for the following grammar
excerpt:

```lex
Expr -> Result<u64, ()>:
      Expr '+' Term { Ok($1? + $3?) }
    | Term { $1 }
    ;
```

we would provide a map `'+' => 'PLUS'` leading, again, to a constant `T_PLUS`
being defined.

One can then write a simple custom lexer which lexes all the input in one go
and returns an `LRNonStreamingLexer` as follows:

```rust
use cfgrammar::NewlineCache;
use lrlex::{lrlex_mod, DefaultLexeme, LRNonStreamingLexer};
use lrpar::{lrpar_mod, Lexeme, NonStreamingLexer, Span};

lrlex_mod!("token_map");
use token_map::*;

fn lex(s: &str) -> LRNonStreamingLexer<DefaultLexeme<u8>, u8> {
  let mut lexemes = Vec::new();
  let mut newlines = NewlineCache::new();
  let mut i = 0;
  while i < s.len() {
    if i == ... {
      lexemes.push(DefaultLexeme::new(T_PLUS, i, ...));
    } else {
      ...
    }
  }
  LRNonStreamingLexer::new(s, lexemes, newlines)
}
```
