# Lexing

Lexing is the act of taking in an input stream and splitting it into lexemes. 
Colloquially, lexing is often described as splitting input into words. In
`grmtools`, a Lexeme has a type (e.g. "INT", "ID"), a value (e.g. "23",
"xyz"), and knows which part of the user's input matched (e.g. "the input
starting at index 7 to index 10"). There is also a simple mechanism to
differentiate lexemes of zero length (e.g. `DEDENT` tokens in Python) from
lexemes inserted by [error recovery](errorrecovery.md).

`lrpar` provides a generic lexing interface to which any lexer can plug into.
Many easy lexing tasks can more easily be carried out by [`lrlex`](lrlex.md), a
`lex` replacement. `lrlex` also provides helper functions which make it [easier
to hand-write lexers](manuallexers.md).
