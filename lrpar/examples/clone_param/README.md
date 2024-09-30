# `clone_param`

## Description
Example which shows how to use interior mutability with the `%parse-param` directive.
As a parameter the parse function accepts a `Rc<RefCell<u64>>`.

## Input 
For input the parser accepts a positive or negative integer e.g. `-1`, `42`, etc followed
by any sequence of `+`, or `-` characters. Except for the initial `-` on a negative integer,
`+` or `-` are treated as `Increment` and `Decrement` operators.

## Evaluation
Rather than building an AST, the param is directly mutated by the actions.
As such an input sequence like `-3++-` will evalute to `-2`.

## Example 
```
>>> -3++-
Evaluated: RefCell { value: -2 }
```
