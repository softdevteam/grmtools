# Error recovery

One of grmtool's most powerful features is its error recovery, which can be used
with any grammar. Continuing the example from [`nimbleparse`](nimbleparse.html),
consider the following syntactically incorrect Lua 5.3 program:

```
$ cat test.lua
x = 0
if x > 0
   print("greater than")
else
   print("less than"}
```

If we use [`nimbleparse`](nimbleparse.html) then the errors are detected and
error recovery attempted. If error recovery is successful then, for each error
location, one or more *repair sequences* are reported. For example on the above
input the following is shown to the user:

```
$ target/release/nimbleparse lua5_3.l lua5_3.y test.lua
...
Error at line 3 col 4. Repair sequences found:
   1: Insert then
Error at line 5 col 21. Repair sequences found:
   1: Insert ), Insert end, Delete }
   2: Insert ), Insert {, Shift }, Insert end
```

`Insert x` means "error recovery inserted a lexeme of type *x*"; `Delete x` means
"error recovery deleted the next lexeme in the stream"; and `Shift x` means
"error recovery kept the user's lexeme *x* as-is".

Intuitively, line 3 should have been `if x > 0 then`. There are two ways of
repairing line 5: it could have been `print("less than") end` (repair sequence
#1) or `print("less than"{}) end` (repair sequence #2). When more than one
repair sequence is presented to the user, the first is used by the algorithm to
continue parsing.

Error recovery requires no extra help from the user and is turned on
automatically ([the underlying algorithm is described
elsewhere](https://arxiv.org/abs/1804.07133)). By default, `Insert` repairs use
lexeme names from the grammar to tell the user what happened. Optionally users
can provide simple annotations to provide more intuitive names. `%epp <lexeme
name> "<pretty print name>"` declarations can be added to the `.y` file e.g.:

```yacc
%epp INT "<int>"
%epp LBRACK "("
```
