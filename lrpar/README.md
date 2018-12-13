# `lrpar`

`lrpar` provides a Yacc-compatible parser (where grammars can be generated at
compile-time or run-time). It can take in traditional `.y` files and convert
them into an idiomatic Rust parser. More details can be found in the [grmtools
book](https://softdevteam.github.io/grmtools/) which includes a quickstart
guide.


## Example

Let's assume we want to statically generate a parser for a simple calculator
language (and let's also assume we are able to use
[`lrlex`](https://softdevteam.github.io/grmtools/lrlex.html) for the lexer). We
need to add a `build.rs` file to our project which tells `lrpar` to statically
compile the lexer and parser files:

```rust
extern crate lrlex;
extern crate lrpar;

use lrlex::LexerBuilder;
use lrpar::{CTParserBuilder, ActionKind};

fn main() -> Result<(), Box<std::error::Error>> {
    let lex_rule_ids_map = CTParserBuilder::new()
        .action_kind(ActionKind::CustomAction)
        .process_file_in_src("calc.y")?;
    LexerBuilder::new()
        .rule_ids_map(lex_rule_ids_map)
        .process_file_in_src("calc.l")?;
    Ok(())
}
```

where `src/calc.l` is as follows:

```
%%
[0-9]+ "INT"
\+ "PLUS"
\* "MUL"
\( "LBRACK"
\) "RBRACK"
[\t ]+ ;
```

and `src/calc.y` is as follows:

```
%start Expr
// Define the Rust type that is to be returned by the actions.
%type u64
%%
Expr: Term 'PLUS' Expr { $1 + $3 }
    | Term { $1 }
    ;

Term: Factor 'MUL' Term { $1 * $3 }
    | Factor { $1 }
    ;

Factor: 'LBRACK' Expr 'RBRACK' { $2 }
      | 'INT' { parse_int($lexer.lexeme_str(&$1.unwrap())) }
      ;
%%
// Any functions here are in scope for all the grammar actions above.

fn parse_int(s: &str) -> u64 {
    match s.parse::<u64>() {
        Ok(val) => val as u64,
        Err(_) => panic!("{} cannot be represented as a u64", s)
    }
}
```

A simple `src/main.rs` is as follows:

```rust
// The cfgrammar import will not be needed once the 2018 edition is stable.
extern crate cfgrammar;
// We import lrpar and lrlex with macros so that lrlex_mod! and lrpar_mod! are in scope.
#[macro_use] extern crate lrpar;
#[macro_use] extern crate lrlex;

use std::io::{self, BufRead, Write};

// Using `lrlex_mod!` brings the lexer for `calc.l` into scope.
lrlex_mod!(calc_l);
// Using `lrpar_mod!` brings the lexer for `calc.l` into scope.
lrpar_mod!(calc_y);


fn main() {
    // We need to get a `LexerDef` for the `calc` language in order that we can lex input.
    let lexerdef = calc_l::lexerdef();
    let stdin = io::stdin();
    loop {
        print!(">>> ");
        io::stdout().flush().ok();
        match stdin.lock().lines().next() {
            Some(Ok(ref l)) => {
                if l.trim().is_empty() {
                    continue;
                }
                // Now we create a lexer with the `lexer` method with which we can lex an input.
                let mut lexer = lexerdef.lexer(l);
                // Pass the lexer to the parser and lex and parse the input.
                let (res, errs) = calc_y::parse(&mut lexer);
                for e in errs {
                    println!("{}", e.pp(&lexer, &calc_y::token_epp));
                }
                match res {
                    Some(r) => println!("Result: {}", r),
                    _ => eprintln!("Unable to evaluate expression.")
                }
            }
            _ => break
        }
    }
}
```

We can now cargo run our project and evaluate simple expressions:

```
>>> 2 + 3
Result: 5
>>> 2 + 3 * 4
Result: 14
>>> (2 + 3) * 4
Result: 20
```

`lrpar` also comes with advanced [error
recovery](https://softdevteam.github.io/grmtools/errorrecovery.html) built-in:

```
>>> 2 + + 3
Parsing error at line 1 column 5. Repair sequences found:
   1: Delete +
   2: Insert INT
Result: 5
>>> 2 + 3 3
Parsing error at line 1 column 7. Repair sequences found:
   1: Delete 3
   2: Insert PLUS
   3: Insert MUL
Result: 5
>>> 2 + 3 4 5
Parsing error at line 1 column 7. Repair sequences found:
   1: Insert MUL, Delete 4
   2: Insert PLUS, Delete 4
   3: Delete 4, Delete 5
   4: Insert MUL, Shift 4, Delete 5
   5: Insert MUL, Shift 4, Insert PLUS
   6: Insert MUL, Shift 4, Insert MUL
   7: Insert PLUS, Shift 4, Delete 5
   8: Insert PLUS, Shift 4, Insert PLUS
   9: Insert PLUS, Shift 4, Insert MUL
Result: 17
```
