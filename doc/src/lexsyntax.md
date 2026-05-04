The syntax of the lrlex `.l` format, aims to be familiar to the format used by posix lex.
It uses the same basic structure as lex.

```
Definitions
%%
Rules
%%
User Subroutines
```

## Definitions

Within the definitions section, you can add an option `%grmtools` section
documented in [extensions](./lexextensions.md)

## Rules 

Each rule is given by the following elements in sequence:

1. Optional Start State, a name given between angle brackets for example `<Start_State>` documented in [Start States](./start_states.md)
2. Regex, syntax defined by the rust [regex](https://docs.rs/regex) crate with optional escaping for any character.
3. Separator space, any horizontal space character in the unicode `Pattern_White_Space` character set
4. Optional State operator, given between angle brackets documented in [Start States](./start_states.md)
    + `<+STATE>` Push the state given by `STATE` to the top of the stack.
    + `<-STATE>` Pop the state off the top of the stack.
    + `<STATE>` Replace the state stack with the state `STATE`
5. Token Name, for example `"token"` any non-space character between double quotes, including double quotes.
6. End of line, finishes each rule.

## User Subroutines

Since lrlex doesn't support user actions, it doesn't support User Subroutines either.