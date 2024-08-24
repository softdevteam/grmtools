# Start States

The following explains the syntax and semantics of Start States in lrlex.<br>
A working example can be found in the repository at [lrpar/examples/start_states][1]

[1]: https://github.com/softdevteam/grmtools/tree/master/lrpar/examples/start_states
## Motivation

Start states are a feature from lex which can be used for context sensitive lexing.
For instance, they can be used to implement nested comments (see the example in the repository).
Such that the tokens start/end markers of tokens maintain balance.

This is achieved by making rules which are qualified to match only when the lexer is in a
particular state. Additionally the lexer has a stack of states, and matching rules perform actions
which modify the stack.

## The INITIAL start state
Unless specified otherwise all lex rules are members of the *INITIAL* start state.

```
%%
<INITIAL>a "A"
<INITIAL>[\t \n]+ ;
```

This is the lex file below with no start states specified.

```
%%
a "A"
[\t \n]+ ;
```

## Rules matching multiple states

Rules can be matched in multiple states, just separate the states a rule should match in commas.
The following matches the `a` character when in either of the states `FirstState` or `SecondState`.

```
<FirstState,SecondState>a "A"
```

## Differences from POSIX lex

In posix lex start states are entered via code in the action, through either `BEGIN(STATE)` and
calling combinations of `yy_push_state`, and `yy_pop_state`.

Because lrlex is actionless, and does not support code actions, instead we have operators to
perform the common modifications to the stack of start states.

### Push
The push operator is given by the adding '+' to the target state on the right hand side within
angle brackets. The following when regex matches in the *CURRENT_STATE* pushes *TARGET_STATE* to
the top of a stack of states.

```
<CURRENT_STATE>Regex <+TARGET_STATE>;
```

### Pop
The pop operator is given by the adding '-' to the target state on the right hand side within angle
brackets. Similarly when in the current state, the following pops the current state off of the
stack of states. Similarly to calling `yy_pop_state` from action code.
```
<CURRENT_STATE>Regex <-CURRENT_STATE>;
```

### ReplaceStack
The ReplaceStack operator is given by naming the target state within angle brackets.
The ReplaceStack op clears the entire stack of states, then pushing the target state.

```
<CURRENT_STATE>Regex <TARGET_STATE>;
```

### Returning a token while performing an operator.
Start state operators can be combined with returning a token for example:

```
<CURRENT_STATE>Regex <+TARGET_STATE>"TOKEN"
```

## Adding a start state
Start stats come in two forms, *exclusive* and *inclusive*. These are given by `%x` and `%s`
respectively.

### Exclusive states
In an exclusive state, the rule can be matched *only* if the rule begins with the state specified.
In the following because `ExclState` is *exclusive*, the `#=` rule is only matched during the
`INITIAL` state, while the `a` and `=#` characters are only matched while in the `ExclState`.

```
%x ExclState
%%

#= <+ExclState>;
<ExclState>a "A"
<ExclState>=# <-ExclState>;
```

### Inclusive states

Inclusive states are added to the set of rules to be matched when the start state is unspecified.

```
%s InclusiveState
%%

a "A"
<InclusiveState>b "B"
<INITIAL>#= <+InclusiveState>;
<InclusiveState>=# <-InclusiveState>;
```

Is equivalent to the following using exclusive states.

```
%x Excl
%%

<INITIAL, Excl>a "A"
<Excl>b "B"
<INITIAL>#= <+Excl>;
<Excl>=# <-Excl>;
```
