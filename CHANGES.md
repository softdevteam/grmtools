# grmtools 0.7.0 (2020-XX-XX)

## Breaking change

* `Lexer` now takes a lifetime `'input` which allows the input to last longer
  than the `Lexer` itself. `Lexer::span_str` and `Lexer::span_lines_str` have
  changed from:
    ```rustc
    fn span_str(&self, span: Span) -> &str;
    fn span_lines_str(&self, span: Span) -> &str;
    ```
  to:
    ```rustc
    fn span_str(&self, span: Span) -> &'input str;
    fn span_lines_str(&self, span: Span) -> &'input str;
    ```
  This change allows users to throw away the `Lexer` but still keep around
  structures (e.g. ASTs) which reference the user's input.

  rustc infers the `'input` lifetime in some situations but not others,
  so if you get an error:
    ```
    error[E0106]: missing lifetime specifier
    ```
  then it is likely that you need to change a type from `Lexer` to
  `Lexer<'input>`.


# grmtools 0.6.2 (2020-03-22)

* Fix two Clippy warnings and suppress two others.

* Prefer "unmatched" rather than "unknown" when using the "turn lexing errors
  into parsing errors" trick.


# grmtools 0.6.1 (2020-03-02)

* Deprecate `Lexeme::len`, `Lexeme::start`, and `Lexeme::end`. Each is now
  replaced by `Lexeme::span().len()` etc. An appropriate warning is generated
  if the deprecated methods are used.

* Avoid use of the unit return type in action code causing Clippy warnings.

* Document the "turn lexing errors into parsing errors" technique and extend
  `lrpar/examples/calc_ast` to use it.


# grmtools 0.6.0 (2020-02-10)

## Breaking changes

* Introduce the concept of a `Span` which records what portion of the user's
  input something (e.g. a lexeme or production) references. Users can turn a
  `Span` into a string through the `Lexer::span_str` function. This has several
  API changes:
   * `lrpar` now exports a `Span` type.
   * `Lexeme`s now have a `fn span(&self) -> Span` function which returns the
     `Lexeme`'s `Span.
   * `Lexer::span_str` replaces `Lexer::lexeme_str` function. Roughly speaking
     this:
       ```rust
       let s = lexer.lexeme_str(&lexeme);
       ```
     becomes:
       ```rust
       let s = lexer.span_str(lexeme.span());
       ```
   * `Lexer::line_col` now takes a `Span` rather than a `usize` and, since a
     `Span` can be over multiple lines, returns `((start line, start column),
     (end line, end column))`.
   * `Lexer::surrounding_line_str` is removed in favour of `span_lines_str`
     which takes a `Span` and returns a (possibly multi-line) `&str` of the
     lines containing that `Span`.
   * The `$span` special variable now returns a `Span` rather than `(usize,
     usize`).

  In practise, this means that in many cases where you previously had to use
  `Lexeme<StorageT>`, you can now use `Span` instead. This has two advantages.
  First, it simplifies your code. Second, it enables better error reporting, as
  you can now point the user to a span of text, rather than a single point. See
  the (new) [AST
  evaluator](https://softdevteam.github.io/grmtools/master/book/ast_example.html)
  section of the grmtools book for an example of how code using `Span` looks.

* The `$span` special variable is now enabled at all times and no longer needs
  to be turned on with `CTBuilder::span_var`. This function has thus been
  removed.


# grmtools 0.5.1 (2020-01-02)

* If called as a binary, lrlex now exits with a return code of 1 if it could
  not lex input. This matches the behaviour of lrpar.

* Module names in generated code can now be optionally configured with
  `mod_name`. The names default to the same naming scheme as before.

* Fully qualify more names in generated code.


# grmtools 0.5.0 (2019-12-17)

## Breaking changes

* `lrlex_mod` and `lrpar_mod` now take strings that match the paths of
  `process_file_in_src`. In other words what was:

    ```rust
    ...
      .process_file_in_src("a/b/grm.y");

    ...

    lrpar_mod!(grm_y);
    ```

  is now:

    ```rust
    ...
      .process_file_in_src("a/b/grm.y");

    ...

    lrpar_mod!("a/b/grm.y");
    ```

  and similarly for `lrlex_mod`. This is hopefully easier to remember and also
  allows projects to have multiple grammar files with the same name.

* The [`Lexer`](https://docs.rs/lrpar/0.4.3/lrpar/trait.Lexer.html) API
  no longer requires mutability. What was:

    ```rust
    trait Lexer {
      fn next(&mut self) -> Option<Result<Lexeme<StorageT>, LexError>>;
      fn all_lexemes(&mut self) -> Result<Vec<Lexeme<StorageT>>, LexError> {
        ...
      }
      ...
    }
    ```

  has now been replaced by an iterator over lexemes:

    ```rust
    trait Lexer {
      fn iter<'a>(&'a self) ->
        Box<dyn Iterator<Item = Result<Lexeme<StorageT>, LexError>> + 'a>;
      ...
    }
    ```

  This enables more ergonomic use of the new zero-copy feature, but does
  require changing structs which implement this trait. `lrlex` has been
  adjusted appropriately. 

  In practise, the only impact that most users will notice is that the following idiom:

    ```rust
    let (res, errs) = grm_y::parse(&mut lexer);
    ```

  will produce a warning that the `mut` part of `&mut` is no longer needed.


## Major changes

* Add support for zero-copying user input when parsing. A special lifetime
  `'input` is now available in action code and allows users to extract parts
  of the input without calling `to_owned()` (or equivalent). For example:

  ```
    Name -> &'input str: 'ID' { $lexer.lexeme_str(&$1.map_err(|_| ())?) } ;
  ```

  See `lrpar/examples/calc_ast/src/calc.y` for a more detailed example.


## Minor changes

* Generated code now uses fully qualified names so that name clashes between
  user action code and that created by grmtools is less likely.

* Action types can now be fully qualified. In other words this:

    ```rust
    R -> A::B:
      ...
      ;
    ```

  means that the rule `R` now has an action type `A::B`.


# grmtools 0.4.3 (2019-11-21)

* Deprecate the MF recoverer: CPCT+ is now the default and MF is now
  undocumented. For most people, CPCT+ is good enough, and it's quite a bit
  easier to understand. In the longer term, MF will probably disappear
  entirely.

* License as dual Apache-2.0/MIT (instead of a more complex, and little
  understood, triple license of Apache-2.0/MIT/UPL-1.0).


# grmtools 0.4.2 (2019-06-26)

* Action code uses `$` as a way of denoting special variables. For example, the
  pseudo-variable `$2` is replaced with a "real" Rust variable by grmtools.
  However, this means that `$2` cannot appear in, say, a string without being
  replaced. This release uses `$$` as an escaping mechanism, so that one can
  write code such as `"$$1"` in action code; this is rewritten to `"$1"` by
  grmtools.


# grmtools 0.4.1 (2019-06-10)

* Newer versions of rustc produce "deprecated" warnings when trait objects are
  used without the `dyn` keyword. This previously caused a large number of
  warnings in generated grammar code from `lrpar`. This release ensures that
  generated grammar code uses the `dyn` keyword when needed, removing such
  warnings.


# grmtools 0.4.0 (2019-05-09)

## Breaking changes

* `Lexeme::empty()` has been renamed to `Lexeme::inserted()`. Although rare,
  there are grammars with empty lexemes that aren't the result of error
  recovery (e.g. DEDENT tokens in Python). The previous name was misleading in
  such cases.

* Lexeme insertion is no longer explicitly encoded in the API for lexemes
  end/length. Previously these functions returned `None` if a lexeme had been
  inserted by error recovery. This has proven to be more effort than it's worth
  with variants on the idiom `lexeme.end().unwrap_or_else(|| lexeme.start())`
  used extensively. These definitions have thus been simplified, changing from:
    ```rust
    pub fn end(&self) -> Option<usize>
    pub fn len(&self) -> Option<usize>
    ```
  to:
    ```rust
    pub fn end(&self) -> usize
    pub fn len(&self) -> usize
    ```

# Major changes

* A new pseudo-variable `$span` can be enabled within parser actions if
  `CTBuilder::span_var(true)` is called. This pseudo-variable has the type
  (usize, usize) where these represent (start, end) offsets in the input
  and allows users to determine how much input a rule has matched.

# Minor changes

* Some dynamic assertions about the correct use of types have been converted to
  static assertions. In the unlikely event that you try to run grmtools on a
  platform with unexpected type sizes (which, in practise, probably only means
  16 bit machines), this will lead to the problems being determined at
  compile-time rather than run-time.


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
