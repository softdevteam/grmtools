# An AST evaluator

We now know enough to put together a more sophisticated version of our simple
calculator example that builds an Abstract Syntax Tree (AST) while parsing,
which is then evaluated separately. This models a common way of building real
compilers. The full example code can be found at
[https://github.com/softdevteam/grmtools/tree/master/lrpar/examples/calc_ast](https://github.com/softdevteam/grmtools/tree/master/lrpar/examples/calc_ast).

The `calc.l` file remains unchanged from that in the [Quickstart
guide](quickstart.md). However the `calc.y` file is change as follows:


```rust,noplaypen
%start Expr
%avoid_insert "INT"
%%
Expr -> Result<Expr, ()>:
      Expr 'PLUS' Term { Ok(Expr::Add{ span: $span, lhs: Box::new($1?), rhs: Box::new($3?) }) }
    | Term { $1 }
    ;

Term -> Result<Expr, ()>:
      Term 'MUL' Factor { Ok(Expr::Mul{ span: $span, lhs: Box::new($1?), rhs: Box::new($3?) }) }
    | Factor { $1 }
    ;

Factor -> Result<Expr, ()>:
      'LBRACK' Expr 'RBRACK' { $2 }
    | 'INT' { Ok(Expr::Number{ span: $span }) }
    ;
%%

use cfgrammar::Span;

#[derive(Debug)]
pub enum Expr {
    Add {
        span: Span,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
    },
    Mul {
        span: Span,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
    },
    Number {
        span: Span
    }
}
```

The most obvious difference here is that we have defined a simple `enum` `Expr`,
with three variants, for our AST. Each AST variant also records a `Span` which
records how much input the AST element covers. By using the
[`$span`](actioncode.md) variable we can ensure that AST elements record their
relationship to portions of the user's input that span multiple tokens (e.g.
for the expressions `1 + 2` the resulting `Expr::Add` will have a `Span`
starting at byte index 0 and ending at byte index 5 -- in other words covering
the complete input string in this case).

After parsing, we thus end up with a `Result<Expr, ()>`. In the case of a
successful parse, this will give us an arbitrarily deeply nested `Expr`.

Our `main.rs` file then looks as follows:

```rust,noplaypen
use std::io::{self, BufRead, Write};

use lrlex::lrlex_mod;
use lrpar::{lrpar_mod, NonStreamingLexer, Span};

lrlex_mod!("calc.l");
lrpar_mod!("calc.y");

use calc_y::Expr;

fn main() {
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
                let lexer = lexerdef.lexer(l);
                let (res, errs) = calc_y::parse(&lexer);
                for e in errs {
                    println!("{}", e.pp(&lexer, &calc_y::token_epp));
                }
                if let Some(Ok(r)) = res {
                    // We have a successful parse.
                    match eval(&lexer, r) {
                        Ok(i) => println!("Result: {}", i),
                        Err((span, msg)) => {
                            let ((line, col), _) = lexer.line_col(span);
                            eprintln!(
                                "Evaluation error at line {} column {}, '{}' {}.",
                                line,
                                col,
                                lexer.span_str(span),
                                msg
                            )
                        }
                    }
                }
            }
            _ => break
        }
    }
}

fn eval(lexer: &dyn NonStreamingLexer<'_, DefaultLexeme, u32>, e: Expr) -> Result<u64, (Span, &'static str)> {
    match e {
        Expr::Add { span, lhs, rhs } => eval(lexer, *lhs)?
            .checked_add(eval(lexer, *rhs)?)
            .ok_or((span, "overflowed")),
        Expr::Mul { span, lhs, rhs } => eval(lexer, *lhs)?
            .checked_mul(eval(lexer, *rhs)?)
            .ok_or((span, "overflowed")),
        Expr::Number { span } => lexer
            .span_str(span)
            .parse::<u64>()
            .map_err(|_| (span, "cannot be represented as a u64"))
    }
}
```

Let's start by running this and seeing what happens:

```
>>> 2+3*4
Result: 14
>>> 2++3*4
Parsing error at line 1 column 3. Repair sequences found:
   1: Delete +
   2: Insert INT
Result: 14
>>> 999999*888888 + 777777*666666
Result: 1407404592594
>>> 9999999999*8888888888 + 7777777777*6666666666
Evaluation error at line 1 column 6, '9999999999*8888888888' overflowed.
```

The first three expressions evaluate just as before. However, the fourth is
interesting: we have explicitly captured the fact that the result of
`9999999999*8888888888` is too big to fit into a `u64`; and not only have we
told the user which character the input starts out, but we've printed out the
precise sub-part of the input which caused that error. This works even when
it's in the middle of the input:

```
>>> 10 + 9999999999*8888888888 + 20
Evaluation error at line 1 column 6, '9999999999*8888888888' overflowed.
```

The key to this is that each AST element knows the `$span` of the production it
is related to; and the resulting `Span` can extract the user's input with
`lexer.span_str(span)`.

Happily, this facility composes nicely with error recovery:

```
>>> 10 ++ 9999999999*8888888888 + 20
Parsing error at line 1 column 5. Repair sequences found:
   1: Delete +
   2: Insert INT
Evaluation error at line 1 column 7, '9999999999*8888888888' overflowed.
```
