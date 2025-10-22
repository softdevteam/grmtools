# Yacc Extensions

At the beginning of a `.y` file is a `%grmtools{}` section, by default this section is required.
But a default can be set or forced by using a `YaccKindResolver`.

| Flag             | Value                                           | Required     |
|------------------|-------------------------------------------------|--------------|
| `yacckind`       |  [YaccKind](yacccompatibility.md#yacckinds)     | &checkmark;  |
| `recoverykind`   |  [RecoveryKind](errorrecovery.md#recoverykinds) | &cross;      |
| `test_files`[^†] |  Array of string values                         | &cross;      |

[^†]: Strings containing globs are resolved relative to the yacc `.y` source file.
      `test_files` is currently experimental.

## Example

```
%grmtools{yacckind: Grmtools}
%%
Start: ;
```
