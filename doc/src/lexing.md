# Lexing

Lexing is the act of taking in an input stream and splitting it into lexemes. 
Colloquially, lexing is often described as splitting input into words. In
`grmtools`, a Lexeme has a type (e.g. "INT", "ID"), a value (e.g. "23",
"xyz"), and knows which part of the user's input matched (e.g. "the input
starting at index 7 to index 10"). There is also a simple mechanism to
differentiate lexemes of zero length (e.g. `DEDENT` tokens in Python) from
lexemes inserted by [error recovery](errorrecovery.md).

Users can write custom lexers that conform to the `lrpar::lex::Lexer` trait.
This API allows users to deal with streaming data since the parser asks the
`Lexer` for one token at a time. However, note that users can later ask the
`Lexer` to return the string from the input matching a lexeme: users need to
buffer input to provide this information.

Hand-written lexers are not particularly difficult to write and, for better or
worse, are necessary for many real-world languages. However, a subset of
languages can use a simpler `lex`/`flex` style approach to lexing, for which
[`lrlex`](lrlex.html) can be used.
