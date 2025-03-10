# Yacc Extensions

At the beginning of a `.y` file is a `%grmtools{}` section, by default this section is required.
But a default can be set or forced by using a `YaccKindResolver`.

## Required flags
    * yacckind

## Example
```
%grmtools{yacckind Grmtools}
%%
Start: ;
```
