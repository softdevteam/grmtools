# Yacc variants

grmtools can deal with several different variants of Yacc input.

## Grmtools

`YaccKind::Grmtools` is grmtools own variant of Yacc syntax. The sole difference
is that rules have a Rust type to which all their production's actions must adhere
to. Consider the following snippet:

```
R -> Result<i32, ()>:
     'a' { Ok(5) }
   | 'b' { Err(()) }
```

Here the rule `R` has a Rust return type of `Result<X, ()>` (between `->` and
`:`). Both of its productions adhere to this type, the first by instantiating
`Ok(5)` and the second `Err(())`.

## “Original” Yacc

Although the name is not fully accurate (grmtools supports a slightly disjoint
subset of original Yacc's input), this mode allows users to most easily test
externally created Yacc files. Several sub-variants are allowed:

* `YaccKind::Original(YaccOriginalActionKind::GenericParseTree)` does not
  execute user actions, but instead creates a generic parse tree, where elements
  are instances of the `lrpar::parser::Node` enum. This is useful for quickly
  testing whether a parser is accepting the intended language.

* `YaccKind::Original(YaccOriginalActionKind::NoActions)` parses input and
  reports errors but does not execute any user actions. This is useful if you
  are trying to test a large corpus of input for correctness.

* `YaccKind::Original(YaccOriginalActionKind::UserAction)` models original Yacc
  most closely but, in a Rust setting, is probably of little use beyond simple
  calculator like languages. Instead of Yacc's `%union` directive, users can
  specify `%actiontype` which is a Rust type which all production actions must
  return an instance of. Unless all actions happen to naturally return the same
  type, this quickly becomes cumbersome to use. For most use cases,
  `YaccKind::Grmtools` is a superior alternative.
