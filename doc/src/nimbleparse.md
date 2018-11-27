# nimbleparse

If you have a [`lrlex`](lrlex.html) compatible `.l` file and an
[`lrpar`](lrpar.html) compatible `.y` file, you can use `nimbleparse` as a quick
way of testing inputs and exploring the resulting parse tree:

```
$ cargo build --release
$ target/release/nimbleparse -h
Usage: nimbleparse [-r <cpctplus|mf|panic|none>] [-y <eco|original>] <lexer.l> <parser.y> <input file>
```

For example, let's assume you are using the Lua 5.3 `.l` and `.y` files from the
[grammars repository](https://github.com/softdevteam/grammars/) you might run
`nimbleparse` as follows:

```
$ cat test.lua
print("Hello world")
$ target/release/nimbleparse lua5_3.l lua5_3.y test.lua
block
 statlistopt
  statlist
   stat
    functioncall
     prefixexp
      var
       NAME print
     args
      LBRACKET (
      explistopt
       explist
        exp
         exp1
          exp2
           exp3
            exp4
             exp5
              exp6
               exp7
                exp8
                 exp9
                  exp10
                   exp11
                    exp12
                     literalstring
                      SHORT_STR "Hello world"
      RBRACKET )
```
