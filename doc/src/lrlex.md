# `lrlex`

`lrlex` is a partial replacement for
[`lex`](http://dinosaur.compilertools.net/lex/index.html) /
[`flex`](https://westes.github.io/flex/manual/). It takes an input string and
splits it into *lexemes* based on a `.l` file. Unfortunately many real-world
languages have corner cases which exceed the power that `lrlex` can provide.
However, when it is suitable, it is a very convenient way of expressing lexing.

See the [quickstart guide](quickstart.html) for more details.
