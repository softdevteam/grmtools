# `lrlex`

`lrlex` is a partial replacement for
[`lex`](http://dinosaur.compilertools.net/lex/index.html) /
[`flex`](https://westes.github.io/flex/manual/). It takes an input string and
splits it into *lexemes* based on a `.l` file. Unfortunately, many real-world
languages have corner cases which exceed the power that `lrlex` can provide.
However, when it is suitable, it is a very convenient way of expressing lexing.

`lrlex` also has a simple command-line interface, allowing you to check whether
your lexing rules are working as expected:

```ignore
$ cat C.java
class C {
    int x = 0;
}
$ cargo run --lrlex java.l /tmp/C.java
    Finished dev [unoptimized + debuginfo] target(s) in 0.18s
     Running `target/debug/lrlex ../grammars/java7/java.l /tmp/C.java`
CLASS class
IDENTIFIER C
LBRACE {
INT int
IDENTIFIER x
EQ =
INTEGER_LITERAL 0
SEMICOLON ;
RBRACE }
```
