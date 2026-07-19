# Multiple start rules

The LR parsing algorithm starts with a single start rule, occasionally 
people find that they want to generate a parser which starts in the middle of some parse rule.
For example, their parser may take a `Sequence` of `Statement` rules. But they also want a version of their
parser to which they can pass a single `Expression`.

## An initial attempt

One of the solutions to this problem is to just copy the parser but change the start rule to the
`Expression` rule. This is a maintenance burden as you end up having multiple copies of your parser.
One way to make this easier to maintain, is to programatically change the start rule. This can be done
with the [clone_and_change_start_rule](https://docs.rs/cfgrammar/latest/cfgrammar/yacc/ast/struct.ASTWithValidityInfo.html#method.clone_and_change_start_rule) function.

### Shortcomings

Each time we clone the grammar rule, we're also duplicating the data parsing data tables used by the algorithm.
This can add up, so at the cost of some complexity we can try another approach to work around the problem.

## A more efficient solution.

At the cost of some complexity to the grammar, we can try a different approach.
To avoid duplicating the internal parser data tables. We'll attempt to use some synthetic tokens, not produced
by the lexer. Then we'll pass these into the parser to kick start the process. This token can be used to select
which subset of the parser we want to start parsing. We will use the `%tokens START_A START_B`, for these
synthetic tokens.

### First steps:

First create a new project, add the dependencies and build dependencies.

```console
cargo new multistart
cd multistart
cargo add lrlex lrpar --build
cargo add lrlex lrpar cfgrammar
```

Here is our grammar `src/multistart.y`

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

We've declared a `meta_start` as our start rule, and it branches to each of the rules which we want to start parsing from.
Branching out based on the initial token.

### Jump starting the parser.

There are a few ways we can try and achieve adding these initial tokens

1. As we've seen previously in the manual, we can write a manual lexer.
2. Use an `lrlex` lexer but wrap the output, adding the initial token.

Lets just build both in one project. The build scripts would be a little bit simpler
if we built them in separate projects. Just refer to the other examples in this book
for a cleaner project structure.

In the future we may explore extensions which make these easier or more efficient.

### With a manual lexer

Intial `build.rs` script.

```rust
use lrlex::{CTTokenMapBuilder, DefaultLexerTypes};
use lrpar::CTParserBuilder;
use std::path::PathBuf;

fn main() {
    let out_dir = PathBuf::from(std::env::var("OUT_DIR").unwrap());

    // 1. Build a token_map for a manual lexer.
    let ctp = CTParserBuilder::<DefaultLexerTypes>::new()
        .grammar_in_src_dir("multistart.y").unwrap()
        .mod_name("multi_manual_y")
        .output_path(out_dir.join("multi_manual.y.rs"))
        .build()
        .unwrap();
    CTTokenMapBuilder::new("token_map", ctp.token_map()).build().unwrap();

    // 2. We'll be adding a wrapped lexer here.
}
```

Calling the parser with a manual lexer:

This is based off the [Hand-written Lexer](manuallexer.md) section, lets start off with the first rule.

```
use cfgrammar::NewlineCache;
use lrlex::{lrlex_mod, DefaultLexeme, DefaultLexerTypes, LRNonStreamingLexer};
use lrpar::{lrpar_mod, Lexeme};

lrpar_mod!("multi_manual.y");
lrlex_mod!("token_map");

use token_map::*;

// For simplicty rather than writing a lexer, lets just build a hard coded list of tokens
// A real example would actually lex things. This just returns a vector of tokens with
// an initial `START_B` token
fn a_rule_lex(s: &str) -> LRNonStreamingLexer<'_, '_, DefaultLexerTypes> {
  let mut lexemes = Vec::new();
  let newlines = NewlineCache::new();

  lexemes.push(Ok(DefaultLexeme::new(T_START_A, 0, 0)));
  lexemes.push(Ok(DefaultLexeme::new(T_A, 0, 1)));
  LRNonStreamingLexer::new(s, lexemes, newlines)
}

fn with_manual_lexer() {
  println!("{:?}", multi_manual_y::parse(&a_rule_lex("A")));

}

fn main() {
  with_manual_lexer();
}
```

Now we can just modify these rules to call into it with the other start token.

```
// Add a second function modified for the `T_START_B` rule.
fn b_rule_lex(s: &str) -> LRNonStreamingLexer<'_, '_, DefaultLexerTypes> {
  let mut lexemes = Vec::new();
  let newlines = NewlineCache::new();

  lexemes.push(Ok(DefaultLexeme::new(T_START_B, 0, 0)));
  lexemes.push(Ok(DefaultLexeme::new(T_B, 0, 1)));
  LRNonStreamingLexer::new(s, lexemes, newlines)
}


fn with_manual_lexer() {
  println!("{:?}", multi_manual_y::parse(&a_rule_lex("A")));
  // Update to add the second entry point.
  println!("{:?}", multi_manual_y::parse(&b_rule_lex("B")));
}
```

### With a wrapper around lrlex

First we need a lexer. We'll include the `START_A` and `START_B` tokens in the grammar, using rules that
cannot match any input characters.

`src/multistart.l`
```
%%
A "A"
B "B"
[\ \n\t] ;
[^\p{any}] "START_A"
[^\p{any}] "START_B"
```


Additions to build.rs

```
use lrlex::CTLexerBuilder;

    // 2. Lets try the same grammar using a lrlex lexer.
    CTLexerBuilder::new()
        
        .lrpar_config(|ctp| {
            ctp.grammar_in_src_dir("multistart.y")
                .unwrap()
                .mod_name("multi_lrlex_y")
                .output_path(out_dir.join("multi_lrlex.y.rs"))
        })
        .lexer_in_src_dir("multistart.l")
        .unwrap()
        .mod_name("multi_lrlex_l")
        .output_path(out_dir.join("multi_lrlex.l.rs"))
        .build()
        .unwrap();
```

The approach we will take is to run the lrlex lexer, and get a list of tokens.
then append that to a vector which contains the start rule.

Here is our function `lrlex_wrapper` which takes an input string, and a start token,
It produces the vector with the start rule as the initial token, followed by each subsequent
token. From that vector it constructs a final `LRNonStreamingLexer` which we can pass to our parser.

Import the modules we generated, and other types and traits we'll need.

```
use lrlex::LRLexError;
use lrpar::Lexer as _;

lrpar_mod!("multi_lrlex.l");
lrpar_mod!("multi_lrlex.y");
```

Here is our wrapper function:

```
fn lrlex_wrapper(s: &str, start_token: u32) -> LRNonStreamingLexer<'_, '_, DefaultLexerTypes> {
    let nl_cache = NewlineCache::new();
    let lexerdef = multi_lrlex_l::lexerdef();
    let mut tokens: Vec<Result<DefaultLexeme, LRLexError>> = vec![Ok(DefaultLexeme::new(start_token, 0, 0))];
    let lexer = lexerdef.lexer(s);
    tokens.extend(lexer.iter());
    LRNonStreamingLexer::new(s, tokens, nl_cache)   
}
```

Modify the main function to call it with some data, and print the results.

```
fn with_lrlex_wrapper() {
    println!("{:?}", multi_lrlex_y::parse(&lrlex_wrapper("A", T_START_A)));
    println!("{:?}", multi_lrlex_y::parse(&lrlex_wrapper("B", T_START_B)));
    // This should parse okay, B is a subset of A, taking either "A", or "B" as input.
    println!("{:?}", multi_lrlex_y::parse(&lrlex_wrapper("B", T_START_A)));

    // This should be an error, as `START_B` only takes "B" as input.
    println!("{:?}", multi_lrlex_y::parse(&lrlex_wrapper("A", T_START_B)));
}

fn main() {
  with_manual_lexer();

  with_lrlex_wrapper();
}
```

