# Yacc variants

grmtools can deal with several different variants of Yacc input.

## Grmtools

`YaccKind::Grmtools` is grmtools' own variant of Yacc syntax, and the one that
most users will want to use. The most significant difference to "normal" Yacc
is that rules are annotated with a Rust type to which all their production's
actions must adhere to. Note that whilst a rule's productions must all adhere
to a single type, different rules can have different types.  Consider the
following snippet:

```
R1 -> Result<i32, ()>:
     'a' { Ok(5) }
   | 'b' { Err(()) }
   ;

R2 -> u64:
   | { 0 }
   ;
```

Here the rule `R1` has a Rust return type of `Result<X, ()>` (between `->` and
`:`). Both of its productions adhere to this type, the first by instantiating
`Ok(5)` and the second `Err(())`. The rule `R2` has a return type of `u64`.


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
  specify `%actiontype` which is a Rust type to which every production's actions
  in the grammar must adhere to. Unless all actions happen to naturally return
  the same type, this quickly becomes cumbersome to use. For most use cases,
  `YaccKind::Grmtools` is a superior alternative.
