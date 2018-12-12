# Parsing

Parsing is the act of checking whether a stream of lexemes match a grammar.
Since a simple "yes/no" answer is rarely useful, it is common to execute
user-defined *actions* during parsing.

`grmtools` contains libraries ([`cfgrammar`](cfgrammar.md) and
[`lrtable`](lrtable.md)) which allow users to build their own LR parsers in
whatever fashion they want. However, for 99% of cases, the [`lrpar`](lrpar.md)
library is what users want and need: a (largely) Yacc-compatible parser. Roughly
speaking, the core parts of grammars work identically in Yacc and `lrpar`, but
some other parts of the system have been modernised (e.g. to avoid the use of
global variables) and given a more idiomatic Rust feel. Notably, `lrpar` is
built from the ground-up to have a powerful, flexible approach to [error
recovery](errorrecovery.md). 


## Actions

Users can specify what sort of actions they want performed when parsing occurs.
The default is `ActionKind::GenericParseTree` which, as its name probably
suggests, creates a generic parse tree, where elements are instances of
the `lrpar::parser::Node` enum.

Most users will probably want to specify `ActionKind::CustomAction`, where each
production can be annotated with an action. A brief example of this is shown in
the [quickstart guide](quickstart.md); a more detailed explanation can be found
in the [error recovery](errorrecovery.md) section.
