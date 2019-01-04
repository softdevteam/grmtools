# Error recovery

One of `lrpar`'s most powerful features is its approach to error recovery, which
can be used with any grammar. This section outlines the background to error
recovery, the choices that users can make, and how to best make use of this
feature.


## Error recovery background

Programmers frequently make mistakes when entering input, either because of
simple typos, or an outright failure to use the correct syntax. Happily, LR
parsing guarantees to report syntax errors at the first point that an error can
be definitively proven to have occurred (though note that this might not be the
same point that a user would consider the error to have been made). It has long
been a goal of parsing technologies to *recover* from such errors, and allow
parsing to continue. This allows users to fix all their syntax errors in one go
and, optionally, post-parsing phases to operate as if no syntax errors had been
made at all. For example, a compiler author might decide to run the compiler's
static type checker even in the presence of syntax errors (since many static
type errors are unaffected by syntax errors), but not generate code (which might
incorrectly give users the illusion that their code is safe to run).

However, most mainstream parsers do a bad job of error recovery. The most common
generic error recovery algorithm is "panic mode" (in reality, a family of
algorithms). Unfortunately such simple error recovery algorithms do a poor job
of recovering from syntax errors, causing a cascade of spurious further syntax
errors to be reported. Programmers quickly learn that only the first reported
syntax error can be trusted on to be correct.

`lrpar` implements the `MF` error recovery algorithm from [Reducing
Cascading Parsing Errors Through Fast Error
Recovery](https://arxiv.org/abs/1804.07133), which, in our biased opinion, does
a better job than previous approaches. It is fast, grammar neutral, and reports
multiple *repair sequences* to users, allowing them to consider which best
matches their intentions.

No matter how clever we think `MF` is, it is important to understand that it has
a fundamental limitation: it only knows about a language's syntax; it has no
concept of the language's semantics beyond that implied by the structure of the
grammar; and it cannot control what the user does with the result of error
recovery. Thus, grammar writers can significantly influence how useful error
recovery is for users. Most of the rest of this section explains how best to
make use of error recovery.


## Error recovery basics

Consider the `calc` grammar from the [quickstart guide](quickstart.html):

```yacc
%start Expr
// Define the Rust type that is to be returned by each
// productions' action.
%actiontype u64
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
// Functions / imports in this section are in scope for
// each productions' actions.

fn parse_int(s: &str) -> u64 {
    match s.parse::<u64>() {
        Ok(val) => val as u64,
        Err(_) => panic!("{} cannot be represented as a u64", s)
    }
}
```

In this grammar, every production has an action: each action *must* evaluate to
an instance of the `%actiontype` type (in this case `u64`). The `$x` variables refer
to the respective symbol in the production (i.e. `$1` refers to the first symbol
in the production). If the symbol is a rule then an instance of `%actiontype` is
stored in the `$x` variable; if the symbol is a lexeme then an `Option<Lexeme>`
instance is returned. A special `$lexer` variable allows access to the lexer.
This allows us to turn `Lexeme`s into strings with the `lexeme_str` function,
which, given a `Lexeme`, returns a `&str` of the relevant part of the user’s
input.

For many examples, this simple grammar and its actions work well leading
to output such as the following:

```
>>> 2 + + 3
Parsing error at line 1 column 5. Repair sequences found:
   1: Delete +
   2: Insert INT
Result: 5
```

`Insert x` means “error recovery inserted a lexeme of type *x*”; `Delete x`
means “error recovery deleted the next lexeme in the stream”; and `Shift x`
means “error recovery kept the user’s lexeme *x* as-is”.

Repair sequences are minimal ways of adjusting the user’s input such that it
becomes correct relative to the underlying grammar. Intuitively, in this
example, the two repair sequences would adjust the input to be equivalent to
`2 + 3` (repair sequence 1) or `2 + <some int> + 3` (repair sequence 2). When
more than one repair sequence is presented to the user, the first is used by the
algorithm to continue parsing: in this case, the input was parsed as if it was
equivalent to `2 + 3`, hence the evaluation of the input to `5`.

Repair sequences can, as their name suggests, be of arbitrary length:

```
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

In this case, the first repair sequence caused the input to be parsed as if it
was equivalent to `2 + 3 * 5`, hence the evaluation of the input to `17`.


## Syntax errors and language semantics

Our example inputs so far have deliberately exploited cases where the first
repair sequence at worst inserted “unimportant” lexemes such as `+` and `*`.
Since the grammar’s actions never read the values of such lexemes, only their
type is important. However, what should happen if error recovery inserts an
integer, whose value is later read by one of the grammar’s actions? An example
shows the unhappy result:

```
>>> 2+
thread 'main' panicked at 'called `Result::unwrap()` on an `Err` value: Lexeme { start: 2, len: 4294967295, tok_id: 4 }', libcore/result.rs:1009:5
note: Run with `RUST_BACKTRACE=1` for a backtrace.
>>> 
```

In this case, the first repair sequence was `Insert INT`. The fundamental
problem is that while error recovery can adjust the user’s input to insert a
lexeme of type `INT`, neither it nor the parser have any idea what value might
have made sense for that lexeme. Thus the expression above caused the expression
`$lexer.lexeme_str(&$1.unwrap())` to panic, since `$1` was `Err(<lexeme>)`.

It is thus up to the user to decide what to do in the face of the inevitable
semantic issues that error recovery highlights. Fortunately, this is generally
simpler than it sounds with only a slight rethink in the way that we tend to
write a grammar's actions.


## A rule of thumb: make `%actiontype` return a `Result` type

Although you can use whatever type you use for `%actiontype`, using a `Result` type
allows a (deliberately) simple interaction with the effects of error recovery.
The basic idea is simple: in actions, we ignore lexemes whose value we don't
care about (e.g. brackets); for lexemes whose value we care about, we either
introduce a default value, or percolate an `Err` upwards. Default values make
sense in certain situations. For example, if you're writing a compiler, and want
to run a static type checker even after syntax errors, it might make sense to
assume that `Insert 0` is a good substitute for `Insert INT`. However, in the
case of the calculator, default values are likely to lead to confusing results.
We thus change the grammar so that inserted integers prevent evaluation from
occurring:

```yacc
%start Expr
%actiontype Result<u64, ()>
%%
Expr: Term 'PLUS' Expr { Ok($1? + $3?) }
    | Term { $1 }
    ;

Term: Factor 'MUL' Term { Ok($1? * $3?) }
    | Factor { $1 }
    ;

Factor: 'LBRACK' Expr 'RBRACK' { $2 }
      | 'INT' {
            let l = $1.map_err(|_| ())?;
            Ok(parse_int($lexer.lexeme_str(&l)))
         }
      ;
%%
fn parse_int(s: &str) -> u64 {
    match s.parse::<u64>() {
        Ok(val) => val as u64,
        Err(_) => panic!("{} cannot be represented as a u64", s)
    }
}
```

The basic idea here is that every action returns an instance of `Result<u64,
()>`: if we receive `Ok(u64)` we successfully evaluated the expression, but if
we received `Err(())` we were not able to evaluate the expression. If we
encounter an integer lexeme which is the result of error recovery, then the
`INT` lexeme in the second `Factor` action will be `Err(<lexeme>)`. By writing
`$1.map_err(|_| ())?` we’re saying “if the integer lexeme was created by error
recovery, percolate `Err(())` upwards”. We then have to tweak a couple of other
actions to percolate errors upwards, but this is a trivial change.

We then need to make a small tweak to our `main.rs` changing:

```rust,ignore
match res {
    Some(r) => println!("Result: {}", r),
    _ => eprintln!("Unable to evaluate expression.")
}
```

to:

```rust,ignore
match res {
    Some(Ok(r)) => println!("Result: {}", r),
    _ => eprintln!("Unable to evaluate expression.")
}
```

Now the input which previously caused a panic simply tells the user that it
could not evaluate the expression:

```ignore
>>> 2+
Parsing error at line 1 column 3. Repair sequences found:
   1: Insert INT
Unable to evaluate expression.
```

Usefully, our inability (or unwillingness) to evaluate the expression does not
prevent further syntax errors from being discovered and repaired:

```ignore
>>> (2+)+3+4+
Parsing error at line 1 column 4. Repair sequences found:
   1: Insert Int
Parsing error at line 1 column 10. Repair sequences found:
   1: Insert Int
Unable to evaluate expression.
```

Using a `Result` type allows the user arbitrary control over the classes of
syntax errors they are prepared to deal with or not. For example, we could
remove the `panic` from `parse_int` by having `%actiontype` be `Result<u64, String>`
where the `Err` case would report a string such as “18446744073709551616 cannot
be represented as a u64” for the first unrepresentable `u64` in the user's
input. If we wanted to report *all* unrepresentable `u64`s, we could have
`%actiontype` by `Result<u64, Vec<String>>`, though merging together the errors found
on the left and right hand sides of the `+` and `*` operators requires adding a
few lines of code.


## Making use of `%epp` for easier to read repair sequences

By default, pretty-printing lexeme types prints out their identifier in the
grammar. These rarely match what the user would expect:

```ignore
>>> 2 3
Parsing error at line 1 column 3. Repair sequences found:
   1: Delete 3
   2: Insert PLUS
   3: Insert MUL
Result: 2
```

What are `PLUS` and `MUL`? These might be semi-obvious, but many lexeme types
are far from obvious. `grmtools` allows users to provide human friendly versions
of these for error recovery using the `%epp` declaration in grammars. For
example, we can extend the `calc` grammar as follows:

```ignore
%epp PLUS "+"
%epp MUL "*"
%epp LBRACK "("
%epp RBRACK ")"
%epp INT "Int"
```

leading to the following output:

```ignore
>>> 2 3
Parsing error at line 1 column 3. Repair sequences found:
   1: Delete 3
   2: Insert +
   3: Insert *
Result: 2
```


## Under the bonnet

For any given syntax error there are, potentially, a finite but vast number of
possible valid repair sequences: far too many to exhaustively search. Error
recovery algorithms such as `MF` use various heuristics to cut the search space
down to something that is (generally) manageable. Although surprisingly few in
practise, this inevitably leads to occasional situations where the repair
sequences found (or, more accurately, those not found) surprise humans.


### Timeout

The first surprising condition is that even with the small `calc` grammar, some
user inputs lead to such a massive search space that no repair sequences can be
found. The easiest way to trigger this in most grammars is bracket expressions:

```ignore
>>> 1+(
Parsing error at line 1 column 4. Repair sequences found:
   1: Insert Int, Insert )
Unable to evaluate expression.
>>> 1+((
Parsing error at line 1 column 5. Repair sequences found:
   1: Insert Int, Insert ), Insert )
Unable to evaluate expression.
>>> 1+(((((((((((
Parsing error at line 1 column 14. No repair sequences found.
Unable to evaluate expression.
```

At a certain number of open brackets (which will partly depend on the speed of
your machine), `MF` simply cannot find suitable repair sequences within its
internal timeout, hence the “No repair sequences found” message. In practise
this happens in less than 2% of real-world inputs, so it is not a significant
worry.


### Some “obvious” repair sequences aren't reported at the end of a file

The second surprising condition is more subtle. Before we can show the issue, we
need to introduce the concept of repair sequence ranking: `MF` only presents the
lowest cost repair sequences to users (where `Insert`s and `Delete`s cost 1, and
`Shift`s cost 0). Higher cost repair sequences are discarded.

In an ideal world, `MF` would find repair sequences that allow a file to parse
completely successfully. In practice, this is only feasible if a syntax error
occurs near the very end of the input. In most cases, `MF` is happy with a
weaker condition, which is that a repair sequence ends with 3 `Shift` repairs,
showing that parsing has got back on track, at least for a little bit. This
condition explains the following:

```ignore
>>> 2 + + 3
Parsing error at line 1 column 5. Repair sequences found:
   1: Delete +
   2: Insert Int
Result: 5
>>> 2 + + 3 +
Parsing error at line 1 column 5. Repair sequences found:
   1: Insert Int
Parsing error at line 1 column 10. Repair sequences found:
   1: Insert Int
Unable to evaluate expression.
```

For `2 + + 3` we match the human intuition that the input could have been `2 +
3` or `2 + <some int> + 3`. However, for the input `2 + + 3 +` we do not report
a `Delete +` repair sequence for the first error in the input. Why?

The first thing we need to know is that repair sequences are always reported
with trailing `Shift` repairs pruned: for the rest of this subsection it aids
understanding to leave them unpruned. Thus, for `2 + + 3`, the two repair
sequences found are `Delete +, Shift 3` and `Insert Int, Shift +, Shift 3`, both
of which cause the entire input to parse successfully, and both of which have
the same cost.

For `2 + + 3 +`, however, the first error leads to 3 repair sequences, `Insert
Int, Shift +, Shift 3, Shift +`, `Delete +, Shift 3, Delete` or `Delete +, Shift
3, Shift +, Insert Int`: the latter two are not even completed since they're
provably higher than the `Insert Int` repair sequence and thus aren’t reported
to the user.

In practise, this situation is rarer than the timeout problem, to the point that
it’s arguably not worth worrying about or explaining to end users. Even when it
happens, the repair sequences that `MF` reports are always correct and at least
one repair sequence will be reported (assuming that error recovery doesn't time
out!).


## Error recovery on real-world grammars

Continuing the example from the [`nimbleparse`](nimbleparse.html) section, we
can see that error recovery works well on arbitrary grammars. Consider the
following syntactically incorrect Lua 5.3 program:

```
$ cat test.lua
x = 0
if x > 0
   print("greater than")
else
   print("less than"}
```

When run through [`nimbleparse`](nimbleparse.html), the following output is
generated:

```
$ caro run --release --bin nimbleparse lua5_3.l lua5_3.y test.lua
...
Error at line 3 col 4. Repair sequences found:
   1: Insert then
Error at line 5 col 21. Repair sequences found:
   1: Insert ), Insert end, Delete }
   2: Insert ), Insert {, Shift }, Insert end
```


## Turning off error recovery

By default, `lrpar` uses the `MF` error recovery algorithm. You can use the
`None` error recovery algorithm, which causes parsing to stop as soon as it hits
the first parsing error, with the `recoverer` method in `CTParserBuilder` or
`RTParserBuilder`. For example, we can change `calc`'s `build.rs` file to:

```rust,ignore
    let lex_rule_ids_map = CTParserBuilder::new()
        .yacckind(YaccKind::Original(YaccOriginalActionKind::UserAction))
        .recoverer(lrpar::RecoveryKind::None)
        .process_file_in_src("calc.y")?;
```

and then no matter how many syntax errors we make, only one is reported:

```
>>> 2++3++
Parsing error at line 1 column 3. No repair sequences found.
Unable to evaluate expression.
```

Unless you have a good reason to do so (e.g. quickly hacking together a grammar
where you would prefer not to think about error recovery at all), we do not
recommend turning off error recovery.
