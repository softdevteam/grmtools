# Lex extensions
    
Flags can be specified at compile time through `LexFlags` or at `.l` file parse time using
a `%grmtools{ }` section. At compile time these flags can be enabled using
[`CTLexerBuilder`](https://docs.rs/lrlex/latest/lrlex/struct.CTLexerBuilder.html) methods.

Flags commonly affect the parsing of the lex file, the interpretation regular expressions,
and set limits.

Boolean flags are specified by their name, and can be negated by prefixing with `!`
other flags should specify their value immediately after the flag name.

## Example
```
%grmtools {
    allow_wholeline_comments
    !octal
    size_limit 1024
}
%%
. "rule"
```
## List of flags:

* `posix_escapes: bool` <p>
    Enable compatibility with posix escape sequences.
* `allow_wholeline_comment: bool`<p>
    Enables c++ style `// comments` at the beginning of a line.
    Subsequently the `/` character may require escaping when used in a regex.

##### Flags passed directly to `regex::RegexBuilder`
* `case_insensitive: bool`
* `dot_matches_new_line: bool`
* `multi_line: bool`
* `octal: bool`
* `swap_greed: bool`
* `ignore_whitespace: bool`
* `unicode: bool`
* `size_limit: usize`
* `dfa_size_limit: usize`
* `nest_limit u32`

## Required flags:
* None at this time.

## Flags affecting Posix compatibility
As discussed in [Lex compatibility](lexcompatibility.md) the default behaviors of grmtools and rust's regex
library have differed from that of posix lex.

The following flags can change the behavior to match posix lex more closely.

```
%grmtools {
    !dot_matches_new_line
    posix_escapes
}
%%
...
```
