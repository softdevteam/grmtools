# grmtools 0.3.1 (2019-04-10)

## Minor changes

* Document lrpar more thoroughly, in particular hiding the inner modules, whose
  location might change one day in the future: all useful structs (etc.) are
  explicitly exposed at the module level.


# grmtools 0.3.0 (2019-03-25)

## Breaking changes

* Have the `process_file` functions in both `LexerBuilder` and
  `CTParserBuilder` place output into a named file (whereas previously
  `CTParserBuilder` expected a directory name).

* Rename `offset_line_col` to `line_col` *and* have the latter return character
  offsets (whereas before it returned byte offsets). This makes the resulting
  numbers reported to humans much less confusing when multi-byte UTF-8
  characters are used.

## Minor changes

* Add `surrounding_line_str` helper function to lexers. This is helpful when
  printing out error messages to users.

* Add a comment with rule names when generating grammars at compile-time. Thus
  if user action code contains an error, it's much easier to relate this to the
  appropriate point in the `.y` file.


# grmtools 0.2.1 (2019-01-16)

* Documentation fixes.


# grmtools 0.2.0 (2019-01-14)

## Breaking changes

* Previously users had to specify the `YaccKind` of a grammar and then the
  `ActionKind` of actions. This is unnecessarily fiddly, so remove `ActionKind`
  entirely and instead flesh out `YaccKind` to deal with the possible variants.
  For example `ActionKind::CustomAction` is now, in essence,
  `YaccKind::Original(YaccOriginalActionKind::UserAction)`. This is a breaking
  change but one that will make future evolution much easier.

* The `%type` directive in grammars exposed by
  YaccKind::Original(YaccOriginalActionKind::UserAction) has been renamed to
  `%actiontype` to make it clear *what* type is being referred to. In general,
  most people will want to move to the `YaccKind::Grmtools` variant (see below),
  which doesn't require the `%actiontype` directive.

## Major changes

* grmtools has moved to the 2018 edition of Rust and thus needs rustc-1.31 or
  later to compile.

* Add `YaccKind::Grmtools` variant, allowing grammar rules to have different
  action types. For most practical use cases, this is much better than
  using `%actiontype`.

* Add `%avoid_insert` directive to bias ranking of repair sequences and make it
  more likely that parsing can continue.

## Minor changes

* Add `-q` switch to `nimbleparse` to suppress printing out the stategraph and
  conflicts (some grammars have conflicts by design, so being continually
  reminded of it isn't helpful).

* Fix problem where errors which lead to vast (as in hundreds of thousands) of
  repair sequences being found could take minutes to sort and rank.

* Add `YaccKind::Original(YaccOriginalActionKind::NoAction)` variant to generate
  a parser which simply tells the user where errors were found (i.e. no actions
  are executed, and not even a parse tree is created).

* `lrlex` no longer tries to create Rust-level identifiers for tokens whose
  names can't be valid Rust identifiers (which led to compile-time syntax
  errors in the generated Rust code).


# grmtools 0.1.1 (2018-12-18)

* Fix bug where `%epp` strings with quote marks in caused a code-generation
  failure in compile-time mode.


# grmtools 0.1.0 (2018-12-13)

First stable release.
