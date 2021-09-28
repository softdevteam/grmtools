# Lexing

Lexing is the act of taking in an input stream and splitting it into lexemes. 
Colloquially, lexing is often described as splitting input into words. In
`grmtools`, a Lexeme has a type (e.g. "INT", "ID"), a value (e.g. "23",
"xyz"), and knows which part of the user's input matched (e.g. "the input
starting at index 7 to index 10"). There is also a simple mechanism to
differentiate lexemes of zero length (e.g. `DEDENT` tokens in Python) from
lexemes inserted by [error recovery](errorrecovery.md).

grmtools provides a "default" lexer in [`lrlex`](lrlex.md), but `lrpar` provides
a generic lexing interface to which any lexer can plug into. Users can provide
one or both of a custom lexeme type -- conforming to
[`lrpar::Lexeme`](https://softdevteam.github.io/grmtools/master/api/lrpar/trait.Lexeme.html)
-- and a custom lexing type -- conforming to
[`lrpar::NonStreamingLexer`](https://softdevteam.github.io/grmtools/master/api/lrpar/trait.NonStreamingLexer.html).
If you wish to use a custom lexer, you will need to instantiate `lrpar`
appropriately (both
[`CTParserBuilder`](https://softdevteam.github.io/grmtools/master/api/lrpar/struct.CTParserBuilder.html)
and
[`RTParserBuilder`](https://softdevteam.github.io/grmtools/master/api/lrpar/struct.RTParserBuilder.html)).
