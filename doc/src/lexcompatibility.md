# Lex compatibility

grmtools currently supports one common use of Lex, which is to produce a
sequence of tokens. All Lex files require at least some porting to grmtools,
though in many cases this is fairly trivial. Nevertheless, aspects such as
the longest match rule are identical to Lex, and we assume familiarity with Lex
syntax and its major features: the [Lex
manual](http://dinosaur.compilertools.net/lex/index.html) is recommended
reading.


## Major differences

There are several major differences between Lex and grmtools:

 * Lex has its own regular expression language whereas grmtools uses the well
   known Rust [regex crate](https://crates.io/crates/regex) for regular
   expressions. These two regular expression languages are very similar, but
   complex regular expressions might not be supported under one or the other.

 * Lex files consist of a sequence of regular expressions and an action for each.
   grmtools lex files consists of a sequence of regular expressions and a token
   name. Actions are not currently supported (and, by extension, nor are
   special action expressions such as `ECHO` and `REJECT`).

 * Both Lex and grmtools lex files support start conditions as an optional prefix
   to regular expressions, listing necessary states for the input expression to 
   be considered for matching against the input. Lex uses a special action
   expression `BEGIN(state)` to switch to the named `state`. grmtools lex files
   use a token name prefix.

 * Character sets, and changes to internal array sizes are not supported by grmtools.
