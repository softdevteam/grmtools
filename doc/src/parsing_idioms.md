# grmtools parsing idioms

grmtools is a flexible tool and can be used in many ways. However, for those
using the `Grmtools` format, the simple idioms below can often make life easier.


## Return `Span`s when possible

When executing grammar actions one is often building up an Abstract Syntax Tree
(AST) or equivalent. For example consider a simple language with assignments:

```
Assign: "ID" "=" Expr;
```

Perhaps the "obvious" way to build this into an AST is to extract the string
representing the identifier as follows:

```rust,noplaypen
Assign -> ASTAssign: "ID" "=" Expr
    {
        let id = $lexer.span_str($1.as_ref().unwrap().span()).to_string();
        ASTAssign::new(id, $3)
    }

%%

struct ASTAssign {
    id: String
}

impl ASTAssign {
    fn new(name: String) -> Self {
        ASTAssign { name }
    }
}
```

This approach is easy to work with, but isn't as performant as may be desired:
the `to_string` call allocates memory and copies part of the user's input into
that. It also loses information about the part of the user's input that the
string relates to.

An alternative approach is not to convert the lexeme into a `String` during
parsing, but simply to return a
[`Span`](https://docs.rs/lrpar/~0/lrpar/struct.Span.html). An outline of this
is as follows:

```rust,noplaypen
Assign -> ASTAssign: "ID" "=" Expr
    {
        ASTAssign { id: $1, expr: Box::new($3.span()) }
    }

%%

type StorageT = u32;

struct ASTAssign {
    id: Span
    expr: Box<Expr>
}

enum Expr { ... }
```

If this is not quite what you want to do, you can use largely the same trick with
the [`Lexeme`](https://docs.rs/lrpar/~0/lrpar/lex/struct.Lexeme.html) `struct`.
Working with `Lexeme`s has the advantage that you can tell what the type of the
lexeme in question is, though generally this is entirely clear from AST
context, and `Lexeme`'s type parameter makes it marginally more fiddly to work
with than `Span`.

Alternatively, if you really want to extract strings during parsing, consider
using the `'input` to extract `&str`'s during parsing, since this does not
cause any additional memory to be allocated.


## Have rules return a `Result` type

As described in the [error recovery
section](errorrecovery.html#a-rule-of-thumb-have-rules-return-a-result-type), it
is generally a good idea to give rules a `Result` return type as this allows
you to easily stop, or change, action code execution if you encounter
"important" inserted lexemes. There are many ways that you can use this, but
many simple cases work well using either:

  * `Err(())` works well if you are creating a parse tree and simply want to
    stop creating the tree when you encounter an important inserted lexeme.

  * `Err(Box<dyn Error>)` works well if you are performing more detailed
    evaluation while parsing and wish to explain to the user why you stopped
    evaluating when you encountered an important inserted lexeme.


### Using `Err(())`

The idea here is that we stop evaluating normal action code by returning
`Err(())`. However, this can lead to endless instances of the following
`map_err` idiom:

```rust,noplaypen
R -> Result<..., ()>:
    "ID" { $1.map_err(|_| ())? }
    ;
```

It can be helpful to define a custom `map_err` function which hides some of this
mess for you:

```rust,noplaypen
R -> Result<Lexeme<StorageT>, ()>:
    "ID" { map_err($1)? }
    ;

%%

fn map_err(r: Result<Lexeme<StorageT>, Lexeme<StorageT>>)
        -> Result<Lexeme<StorageT>, ()>
{
    r.map_err(|_| ())
}
```


### Using `Err(Box<dyn Error>)`

The idea here is that we both stop evaluating normal action code, and explain
why, by returning `Err(Box<dyn Error>)`. Although `Box<dyn Error>` is something
of a mouthful, it allows you significant flexibility in *what* you return in
error situations. If you want to quickly experiment, then this is convenient
because the token type `Result<Lexeme<StorageT>, Lexeme<StorageT>>` can be
automatically coerced to `Box<dyn Error>` (e.g. `$1?` in action code will
return the `Err` variant without additional code). You can also return
strings-as-errors with `Box::<dyn Error>::from("...")`.

Using this idiom we can change our calculator example to deal with many more
possible sources of error:

```rust,noplaypen

%start Expr
%avoid_insert "INT"
%%
Expr -> Result<u64, Box<dyn Error>>:
      Factor '+' Expr
      {
          Ok($1?.checked_add($3?)
              .ok_or(Box::<dyn Error>::from("Overflow detected."))?)
      }
    | Factor { $1 }
    ;

Factor -> Result<u64, Box<dyn Error>>:
      Term '*' Factor
      {
          Ok($1?.checked_mul($3?)
              .ok_or(Box::<dyn Error>::from("Overflow detected."))?)
      }
    | Term { $1 }
    ;

Term -> Result<u64, Box<dyn Error>>:
      '(' Expr ')' { $2 }
    | 'INT'
      {
          parse_int(
              $lexer.span_str(
                  $1.map_err(|_| "<evaluation aborted>")?.span()))
      }
    ;
%%
// Any imports here are in scope for all the grammar actions above.

use std::error::Error;

fn parse_int(s: &str) -> Result<u64, Box<dyn Error>> {
    match s.parse::<u64>() {
        Ok(val) => Ok(val),
        Err(_) => {
            Err(Box::from(
                format!("{} cannot be represented as a u64", s)))
        }
    }
}
```


## Define a `flatten` function

Yacc grammars make specifying sequences of things something of a bore. A common
idiom is thus:

```rust,noplaypen
ListOfAs -> Result<Vec<A>, ()>:
      A { Ok(vec![$1?]) }
    | ListOfAs A
      {
          let mut $1 = $1?;
          $1.push($1?);
          Ok($1)
      }
    ;

A -> Result<A, ()>: ... ;
```

Since this idiom is often present multiple times in a grammar, it's generally
worth adding a `flatten` function to hide some of this:

```rust,noplaypen
ListOfAs -> Result<Vec<A>, ()>:
      A { Ok(vec![$1?]) }
    | ListOfAs A { flatten($1, $2) }
    ;

A -> Result<A, ()>: ... ;
%%

fn flatten<T>(lhs: Result<Vec<T>, ()>, rhs: Result<T, ()>)
           -> Result<Vec<T>, ()>
{
    let mut flt = lhs?;
    flt.push(rhs?);
    Ok(flt)
}
```

Note that `flatten` is generic with respect to `T` so that it can be used in
multiple places in the grammar.


## Composing idioms

The above idioms compose well together. For example, `flatten`, `map_err`, and
`Lexeme` can be used together as shown in the following example:

```rust,noplaypen
ListOfIds -> Result<Vec<Lexeme<StorageT>>, ()>:
      "ID" { Ok(vec![map_err($1)?]) }
    | ListOfIds "Id" { flatten($1, map_err($2)?) }
    ;

%%

type StorageT = u32;

fn map_err(r: Result<Lexeme<StorageT>, Lexeme<StorageT>>)
        -> Result<Lexeme<StorageT>, ()>
{
    r.map_err(|_| ())
}

fn flatten<T>(lhs: Result<Vec<T>, ()>, rhs: Result<T, ()>)
           -> Result<Vec<T>, ()>
{
    let mut flt = lhs?;
    flt.push(rhs?);
    Ok(flt)
}
```
