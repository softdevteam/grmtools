# grmtools parsing idioms

grmtools is a flexible tool and can be used in many ways. However, for those
using the `Grmtools` format, the simple idioms below can often make life easier.


# Return `Span`s when possible

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


# Have rules return a `Result` type and add a function to avoid `map_err` directly

As described in the [error recovery
section](errorrecovery.html#a-rule-of-thumb-have-rules-return-a-result-type), it
is generally a good idea to give rules a `Result` return type. This allows a
simple interaction with error recovery. However, it can lead to endless
instances of the following `map_err` idiom:

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


# Define a `flatten` function

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


# Composing the idioms

Happily, `flatten`, `map_err`, and `Lexeme` combine well:

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
