# Multiple start rules

lrpar parsers start with a single start rule, this chapter discusses
the case where you want _multiple_ start rules.

## Simulating multiple start rules

An approach to simulating multiple start rules from a single start rule
is to synthesize tokens not produced by the lexer as initial start tokens.
Then produce those as the initial token passed to the parser to select between
parser entry points.

### Initial project
First create a new project, add the dependencies and build dependencies.

```console
cargo new multistart
cd multistart
cargo add lrlex lrpar --build
cargo add lrlex lrpar cfgrammar
```

### Parser
Here is our grammar `src/multistart.y` the tokens `START_A` and `START_B` are
our synthetic tokens. While `ARule` and `BRule` are our different start rules
we want to select between.

```
%grmtools{yacckind: Grmtools}
%token START_A START_B
%start meta_start
%%
meta_start -> Result<String, DefaultLexeme> :
  START_A ARule { $2 }
| START_B BRule { $2 }
;

ARule -> Result<String, DefaultLexeme>
: 'A' { Ok($lexer.span_str($1?.span()).to_string()) }
| BRule { $1 }
;

BRule -> Result<String, DefaultLexeme>
: 'B' { Ok($lexer.span_str($1?.span()).to_string()) }
;
%%
use lrlex::DefaultLexeme;
```

### Lexer

In our lexer we'll need to add a directive to advise that the checker that we expect the missing tokens.

```
%expect-missing "START_A" "START_B"
%%
A "A"
B "B"
[\ \n\t] ;
```

Following this we'll need to prepend one of the start tokens to the lexical analysis phase.
To indicate which parse rule we expect to use as the start rule. For that we'll need a `token_map`.

### Build.rs

```rust
use lrlex::{CTLexerBuilder, CTTokenMapBuilder, DefaultLexerTypes};
use lrpar::CTParserBuilder;

fn main() {
    // In addition to the usual parser, and lexer
    // We'll need a token map for our synthetic tokens.
    let ctp = CTParserBuilder::<DefaultLexerTypes>::new()
        .grammar_in_src_dir("multistart.y")
        .unwrap()
        .build()
        .unwrap();
    CTLexerBuilder::new()
        .rule_ids_map(ctp.token_map())
        .lexer_in_src_dir("multistart.l")
        .unwrap()
        .build()
        .unwrap();
    CTTokenMapBuilder::new("token_map", ctp.token_map())
        .allow_dead_code(true)
        .build()
        .unwrap();
}
```

### Wrapping the lexer

Finally we'll need to:

1. Run our input text through the parser.
2. Prepend the selected start token.
3. Run the parser with the combined tokens.

```rust
use cfgrammar::NewlineCache;
use lrlex::LRLexError;
use lrlex::{DefaultLexeme, DefaultLexerTypes, LRNonStreamingLexer, lrlex_mod};
use lrpar::Lexer as _;
use lrpar::{Lexeme, lrpar_mod};

lrlex_mod!("multistart.l");
lrpar_mod!("multistart.y");

lrlex_mod!("token_map");
use token_map::{T_START_A, T_START_B};

fn lrlex_wrapper(s: &str, start_token: u32) -> LRNonStreamingLexer<'_, '_, DefaultLexerTypes> {
    let nl_cache = NewlineCache::new();
    let lexerdef = multistart_l::lexerdef();
    let mut tokens: Vec<Result<DefaultLexeme, LRLexError>> =
        vec![Ok(DefaultLexeme::new(start_token, 0, 0))];
    let lexer = lexerdef.lexer(s);
    tokens.extend(lexer.iter());
    LRNonStreamingLexer::new(s, tokens, nl_cache)
}

fn main() {
    assert!(
        multistart_y::parse(&lrlex_wrapper("A", T_START_A))
            .0
            .is_some()
    );
    assert!(
        multistart_y::parse(&lrlex_wrapper("B", T_START_B))
            .0
            .is_some()
    );
    // This should parse okay, since `START_A` takes either "A", or "B" as input.
    assert!(
        multistart_y::parse(&lrlex_wrapper("B", T_START_A))
            .0
            .is_some()
    );

    // However the following should error since `START_B` only takes "B" as input.
    assert!(
        !multistart_y::parse(&lrlex_wrapper("A", T_START_B))
            .1
            .is_empty()
    );
}
```