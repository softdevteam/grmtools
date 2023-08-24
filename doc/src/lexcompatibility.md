# Lex compatibility

grmtools currently supports one common use of Lex, which is to produce a
sequence of tokens. All Lex files require at least some porting to grmtools,
though in many cases this is fairly trivial. Nevertheless, aspects such as
the longest match rule are identical to Lex, and we assume familiarity with Lex
syntax and its major features: the [Lex
manual](https://web.archive.org/web/20220402195947/dinosaur.compilertools.net/lex/index.html) is recommended
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

 * Escape sequences:

   In addition to escape sequences involved in the escaping of regular expressions.
   Lex and grmtools support the escape sequences `\123` (octal) `\x1234` (hexadecimal)
   and ASCII escape sequences. `\\` `\a` `\f` `\n` `\r` `\t` `\v`.

   Lex also interprets the escape sequence `\b` as `backspace`.  While regex treats `\b`
   as a word boundary subsequently grmtools will too.

   Additional escape sequences supported by regex:

   The `\u1234` and `\U12345678` escape sequences for unicode characters,
   the `\p`,`\P` unicode character classes, as well as the `\d` `\D` `\s` `\S`
   `\w` `\W` perl character classes, and `\A` `\b` `\B` `\z` escape sequences.

   Both Lex and grmtools support escaping arbitrary characters, for all other characters
   besides those listed above, when given an escaped character `\c` it will be passed to
   the regex engine as the character `c`.  This is useful when a character is used within
   the lex format.

   An example of this is when the character `<` is used at the beginning of a regex. Both Lex
   and grmtools interpret this as the beginning of a start condition prefix. Which can be
   escaped with `\<` to ensure it is treated as the start of a regular expression.

   But the characters to which this behavior applies is impacted by the escape sequence
   differences listed above.

* Lex treats lines in the rules section beginning with whitespace as code to be copied verbatim
  into the generated lexer source.  Grmtools lex does not support these and produces an error. 
