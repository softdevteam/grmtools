# Lexing

Lexing is the act of taking in an input stream and splitting it into lexemes. 
Colloquially, lexing is often described as splitting input into words. In
`grmtools`, a Lexeme has a type (e.g. "INT", "ID"), a value (e.g. "23",
"xyz"), and knows which part of the user's input matched (e.g. "the input
starting at index 7 to index 10"). There is also a simple mechanism to
differentiate lexemes of zero length (e.g. `DEDENT` tokens in Python) from
lexemes inserted by [error recovery](errorrecovery.md).

A subset of languages can use a simple `lex`/`flex` style approach to lexing,
for which [`lrlex`](lrlex.html) can be used. For situations which require more
flexibility, users can write their own custom lexer provided it implements the
[`lrpar::lex::NonStreamingLexer`](https://softdevteam.github.io/grmtools/master/api/lrpar/trait.NonStreamingLexer.html)
trait.
