# `cfgrammar`

`cfgrammar` reads in grammar files, processes them, and provides a convenient
API for operating with them. Most users only need to think about `cfgrammar` to the
extent that they are required to use it to specify what Yacc variant they wish
to use.

`cfgrammar` may also be of interest to those manipulating grammars directly, or
who wish to use custom types of parsers. Note that `cfgrammar`'s API should be
considered semi-stable at best. As the needs of other parts of grmtools change,
`cfgrammar` tends to have to change too. Since it is unlikely to have few direct
users, the consequences of changing the API are relatively slight.
