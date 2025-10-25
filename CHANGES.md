# grmtools 0.14.0 (2025-10-22)

This release contains a number of new features and breaking changes. Most of
the breaking changes are in advanced/niche parts of the API, which few users
will notice. However, four breaking changes might affect a more substantial
subset of users: those are highlighted in the "breaking changes (major)"
section below.


## New features and improvements

 * Lex and Yacc-like inputs can now optionally take a `%grmtools` directive
   which allows customisation of how grmtools treats the file. This allows
   users to keep together the necessary grmtools settings, rather than
   having to remember what is set in, for example, a `build.rs` file. See
   [Lex Extensions](https://softdevteam.github.io/grmtools/latest_release/book/lexextensions.html)
   and [Yacc Extensions](https://softdevteam.github.io/grmtools/latest_release/book/yaccextensions.html)
   in the grmtools book for more details. `nimbleparse` is
   also able to use `%grmtools` directives.

   Note that setting options via the command-line / build script overrides
   `%grmtools` directives.

 * Many error messages have been improved, ranging from incorrect grammars
   to reporting the look ahead value with reduce/reduce conflicts.

 * lrpar uses bincode directly for generated tables, making the serde
   dependency optional.

 * `parse_map` been added as a more generic version of `parse_generictree`. The
   latter is marked as deprecated.

 * `CTTokenMapBuilder` has been added as a more flexible alternative to
   `ct_token_map`. The latter is marked as deprecated.

 * lrlex has a new flag `allow_wholeline_comments` which allows `// ...`
   comments to be added to lex files. This defaults to off, because it is not
   uncommon for Lex rules themselves to use `//`.

 * Support for use under WASM has been improved.


## Breaking changes

 * `LexErrorKind is no longer `Eq`/`PartialEq`. This allows specific errors
   with regexes to be reported, instead of the generic error previously.

 * Many `struct`s and `enum`s have been marked non-exhaustive. This means that
   external users cannot directly construct instances of such types. In general,
   these are parts of the API that users would have expected to have received
   from grmtools, not construct themselves.

 * `allow_missing_tokens_in_parser` is now treated as a warning.

 * `RegexOptions` in lrlex has been renamed `LexFlags`. This struct was, and
   remains, mostly `doc(hidden)` but it cannot be fully hidden from users.


## Other changes

 * Code generation now uses the
   [quote](https://crates.io/crates/quote) crate and formatted using
   [prettyplease](https://crates.io/crates/prettyplease). This makes dealing
   with the generated code more pleasant.

 * The signature for `ct_token_map` has been generalized to use the `Borrow`
   trait instead of a reference.

 * The lifetime of the `lrpar_config` callback has been relaxed (previously it
   was the onerous `'static`).


# grmtools 0.13.10 (2025-02-04)

 * Add option for more complete POSIX lex compatible regex escapes. For
   example, `\b` is the backspace character in POSIX Lex, but a word boundary
   association in the Rust [regex](https://crates.io/crates/regex) crate that
   lrlex uses. This defaults to `false` for backwards compatibility.


# grmtools 0.13.9 (2025-02-04)

* Respect the timeout in all stages of error recovery. Previously the timeout
  only applied to the first of (several!) stages of error recovery, which could
  lead to a comically long time spent in the latter stages.

* Add accessor functions for overly `pub` fields in `lrlex::Rule`. Accessing
  the fields directly now causes a deprecation warning.

* New `-d` option for `nimbleparse` outputs the stategraph.


# grmtools 0.13.8 (2024-11-07)

* `%parse-param` can now use types that implement `Clone` (i.e. relaxing the
  previous stringent requirement that types were `Copy`).

* Document start states in the grmtools book.

* Allow `lrlex` and `nimbleparse` to read from stdin if the path is `-`.


# grmtools 0.13.7 (2024-06-14)

* Catch incorrectly terminated productions. Previously this led to a confusing
  situation where productions could be merged together.

* Give better warnings if lexer/grammar can't be read at build time.


# grmtools 0.13.6 (2024-05-30)

* Allow `%prec` to define a new token in the grammar. Previously if `%prec 'x'`
  was the first mention of "x" then an error would be raised.

* Tell the user where an incomplete action in a grammar started, not finished
  (since it always "finishes" at the end of the file).


# grmtools 0.13.5 (2024-05-04)

* Improve error messages for conflicts and the like, giving the span of input
  related to the error.


# grmtools 0.13.4 (2024-01-04)

* Change generated code to avoid errors about `unsafe` action code in input
  grammars.

* Hide unstable parts of the API behind an `_unstable_api` feature that is off
  by default.


# grmtools 0.13.3 (2023-09-21)

* lrlex now explicitly raises an error when a rule in an input file
  has leading space. There is a small chance of this breaking existing input
  files, but it brings lrlex into line with POSIX lex where leading
  space indicates verbatim code (a concept for which lrlex currently has no
  support), making porting errors less likely.

* Report errors on `%epp` declarations in terms of the input file (rather than
  pretending they're all at line 1, column 1).

* Reorganise internal testing framework.


# grmtools 0.13.2 (2023-08-01)

* Add CTLexerBuilder options for configuring regex behavior.


# grmtools 0.13.1 (2023-01-27)

* Support `%empty` in productions. This Bison-ism can be used as a signal to
  readers that a production really is meant to be empty.

* Allow rules to be repeated, with each being treated as a separate
  production(s). In other words this grammar:

  ```
  A: 'x';
  A: 'y';
  ```

  is now equivalent to:

  ```
  A: 'x' | 'y';
  ```


# grmtools 0.13.0 (2023-01-19)

This release contains a number of new features and breaking changes. Most of
the breaking changes are in advanced/niche parts of the API, which few users
will notice. However, four breaking changes might affect a more substantial
subset of users: those are highlighted in the "breaking changes (major)"
section below.


## New features

* Improved error messages, with various parts of grammar and lexer files now
  carrying around `Span` information to help pinpoint errors.

* A single error can be related to multiple `Span`s. For example, if you
  duplicate a rule name in a grammar, all duplicates are reported in a single
  error.

* The new `cfgrammar::NewlineCache` struct makes it easier to store the
  minimal information needed to convert byte offsets in an input into logical
  line numbers.

* lrlex now supports start states.

* Unused tokens / rules in a grammar are now detected and, by default, reported
  as errors. The `%expect-unused` can suppress such warnings on a
  per-token/rule basis.


## Breaking changes (major)

* Start states mean that lrlex now interprets `<` in the regular expression
  differently than before: to restore the previous behaviour, escape `<` with
  `\`. For example, the lrlex rule `< "<"` now appears to lrlex as an
  incomplete start state: replacing it with `\< "<"` fixes the problem.

* grmtools now bundles many of its type parameters into a `LexexTypes` trait,
  to avoid forcing users to endlessly repeat multiple arguments. If you
  specified a custom `StorageT` with lrlex/lrpar then you will need to
  change idioms such as `DefaultLexeme<StorageT>, StorageT>` to
  `DefaultLexerTypes<StorageT>`. For example, you might need to change:
  ```
  use lrlex::{DefaultLexeme, LRNonStreamingLexer};
  ...
  lexer: &LRNonStreamingLexer<DefaultLexeme<StorageT>, StorageT>,
  ```
  to:
  ```
  use lrlex::{DefaultLexerTypes, LRNonStreamingLexer};
  ...
  lexer: &LRNonStreamingLexer<DefaultLexerTypes<StorageT>>,
  ```

* Unused tokens / rules in a grammar are now detected and, by default, reported
  as errors. For example, the common "trick" to turn lexing errors into parsing
  errors [suggests adding the following to a grammar](https://softdevteam.github.io/grmtools/latest_release/book/errorrecovery.html#turning-lexing-errors-into-parsing-errors):
  ```
  Unmatched -> ():
    "UNMATCHED" { } 
  ;
  ```
  Both the `Unmatched` rule and the `UNMATCHED` token will be reported as unused.
  You can tell grmtools that you expect this to happen with the `%expect-unused`
  directive:
  ```
  %expect-unused Unmatched "UNMATCHED"
  ```

* `StorageT` is now used to represent parser states (whereas before it was
  hard-coded to a `u16`). If you used a custom `StorageT`, it may no longer be
  big enough: if this happens, an error will be reported while the grammar is
  being built. You will then need to increase the size of your `StoargeT` (e.g.
  you might need to change `StorageT` from `u8` to `u16`).


## Breaking changes (minor)

* Serde support for lrpar now requires enabling the `serde` feature.

* `cfgrammar::yacc::grammar::YaccGrammar::token_span` now returns
  `Option<Span>` rather than `Option<&Span>`.

* `cfgrammar::yacc::ast::{Production, Symbol}` no longer derive `Eq`, `Hash`,
  and `PartialEq`. Since both now carry a `Span`, it's easy to confuse "two
  {productions, symbols} have the same name" with "at the same place in the
  input file."

* `cfgrammar::yacc::ast::add_rule`'s signature has changed from:
  ```
    pub fn add_rule(&mut self, name: String, actiont: Option<String>) {
  ```
  to:
  ```
    pub fn add_rule(&mut self, (name, name_span): (String, Span), actiont: Option<String>) {
  ```

* `GrammarValidationError` and `YaccParserError` have been combined into a
  struct `YaccGrammarError` (which replaces the previous enum of that name).
  The new `YaccGrammarError` has a private enum, so will mean fewer
  semver-breaking changes.

* `LexBuildResult` returns on failure `Err(Vec<LexBuildError>)` rather than
  `Err(LexBuildError)`.

* The `lrlex::lexemes` module has been renamed to `lrlex::defaults` to better
  describe what it is providing.


## Deprecations

* `Span` has moved from `lrpar` to `cfgrammar`. The import is still available
  via `lrpar` but is deprecated (though due to
  https://github.com/rust-lang/rust/issues/30827 this unfortunately does not
  show as a formal deprecation warning).

* `cfgrammar::yacc::grammar::YaccGrammar::rule_name` has been renamed to
  `rule_name_str`. The old name is still available but is deprecated.


# grmtools 0.12.0 (2022-04-14)

* Move to Rust 2021 edition.

* Various minor clean-ups.


# grmtools 0.11.1 (2021-12-07)

* Explicitly error if the users tries to generate two or more lexers or parsers
  with the same output file name. Previously the final lexer/parser created
  "won the race", leading to a confusing situation where seemingly correct code
  would not compile. Users can explicitly set an output path via `output_path`
  that allows multiple lexers/parsers to be generated with unique names.


# grmtools 0.11.0 (2021-11-18)

An overview of the changes in this version:
  * `Lexeme` is now a trait not a struct, increasing flexibility, but requiring
    some changes in user code.
  * The build API has slightly changed, requiring some changes in user code.
  * `%parse-param` is now supported.
  * `lrlex` provides a new API to make it easy to use simple hand-written
    lexers instead of its default lexer.

## Breaking changes

### `Lexeme` is now a trait not a struct

`lrpar` now defines a `Lexeme` *trait* not a `Lexeme` *struct*: this allows the
parser to abstract away from the particular data-layout of a lexeme (allowing,
for example, a lexer to attach extra data to a lexeme that can be accessed by
parser actions) but does add an extra type parameter `LexemeT` to several
interfaces. Conventionally the `LexemeT` type parameter precedes the `StorageT`
type parameter in the list of type parameters.

`lrlex` defaults to using its new `DefaultLexeme` struct, which provides a
generic lexeme struct similar to that previously provided by `lrlex` (though
note that you can use `lrlex` with a lexeme struct of your own choosing).

The precise effects of these changes will depend on how you use grmtools'
libraries but in general:

* You will need to change your lexeme imports from:
  ```rust
    use lrpar::Lexeme;
  ```
  to:
  ```rust
    use lrlex::DefaultLexeme;
    use lrpar::Lexeme;
  ```

* Most references to `Lexeme` will need to refer to `DefaultLexeme`.

* Any references to `LRNonStreamingLexer` will need to change from:
  ```rust
    LRNonStreamingLexer<Lexeme<u32>>
  ```
  to:
  ```rust
    LRNonStreamingLexerDef<DefaultLexeme<u32>, u32>
  ```
  where `u32` is the `StorageT` of your choice.

One of the additional benefits to this change is that it allows `lrpar` and
other lexers (e.g. `lrlex`) to be clearly separated: `lrpar` now only defines
traits which lexers have to conform to.


### Build API changes

Several of the functions / structs surrounding the compile-time construction
of grammars have changed: more details are given below, but in most cases
a `build.rs` that looks as follows:

```rust
  use cfgrammar::yacc::YaccKind;
  use lrlex::LexerBuilder;
  use lrpar::CTParserBuilder;

  fn main() -> Result<(), Box<dyn std::error::Error>> {
      let lex_rule_ids_map = CTParserBuilder::<u8>::new_with_storaget()
          .yacckind(YaccKind::GrmTools)
          .process_file_in_src("calc.y")?;
      LexerBuilder::new()
          .rule_ids_map(lex_rule_ids_map)
          .process_file_in_src("calc.l")?;
      Ok(())
  }
```
can be changed to:
```rust
  use cfgrammar::yacc::YaccKind;
  use lrlex::CTLexerBuilder;
  
  fn main() -> Result<(), Box<dyn std::error::Error>> {
      CTLexerBuilder::new()
          .lrpar_config(|ctp| {
              ctp.yacckind(YaccKind::Grmtools)
                  .grammar_in_src_dir("calc.y")
                  .unwrap()
          })
          .lexer_in_src_dir("calc.l")?
          .build()?;
      Ok(())
  }
```

In more detail:

* `lrlex`'s `LexerBuilder` has been renamed to `CTLexerBuilder` for symmetry with
  `lrpar`.

* `CTLexerBuilder` now provides the `lrpar_config` convenience function which
  removes some of the grottiness involved in tying together an `lrlex` lexer
  and `lrpar` parser. `lrpar_config` is passed a `CTParserBuilder` instance to
  which normal `lrpar` compile-time options can be applied.

* `CTParserBuilder::process_file_in_src` is deprecated in favour of
  `CTParserBuilder::grammar_in_src_dir` and `CTParserBuilder::build`. The
  latter method consumes the `CTParserBuilder` returning a `CTParser` which
  exposes a `token_map` method whose result can be passed to lexers such as
  `lrlex`. 

  The less commonly used `process_file` function is similarly deprecated in
  favour of the `grammar_path`, `output_path`, and `build` functions.

* `LexerBuilder::process_file_in_src` is deprecated in favour of
  `LexerBuilder::lexer_in_src_dir` and `LexerBuilder::build`.

  The less commonly used `process_file` function is similarly deprecated in
  favour of the `lexer_path`, `output_path`, and `build` functions.

* `CTLexerBuilder`'s and `CTParserBuilder`'s `build` methods both consume the
  builder, producing a `CTLexer` and `CTParser` respectively, which can be
  queried for additional information.


### The conflicts API has moved

* The unstable `CTParserBuilder::conflicts` method has moved to `CTParser`.
  This interface remains unstable and may change without notice.

## New features

* Yacc grammars now support the `%parse-param <var>: <type>` declaration. The
  variable `<var>` is then visible in all action code. Note that `<type>` must
  implement the [`Copy`
  trait](https://doc.rust-lang.org/std/marker/trait.Copy.html). The generated
  `parse` function then takes two parameters `(lexer: &..., <var>: <type>)`.

* `lrlex` now exposes a `ct_token_map` function which creates a module with
  a parser's token IDs, and allows users to call `LRNonStreamingLexer::new`
  directly. This makes creating simple hand-written lexers much easier (see
  the new `calc_manual_lex` example to see this in action).


# grmtools 0.10.2 (2021-08-09)

* Optimise `NonStreamingLexer::span_lines_str` from *O(n)* to *O(log n)*.

* Deprecate GrammarAST::add_programs in favour of GrammarAST::set_programs.


# grmtools 0.10.1 (2021-05-11)

* Add support for Yacc's `%expect` and Bison's `%expect-rr` declarations. These
  allow grammar authors to specify how many shift/reduce and reduce/reduce
  conflicts they expect in their grammar, and to error if either quantity is
  different, which is a more fine-grained check than the `error_on_conflicts`
  boolean.

* Generate code with "correct" camel case names to avoid Clippy warnings in
  code that uses grmtools' output.


# grmtools 0.10.0 (2021-03-29)

## Breaking changes

* A number of previously public items (functions, structs, struct attributes)
  have been made private. Most of these were either not externally visible, or
  only visible if accessed in undocumented ways, but some were incorrectly
  public.


# grmtools 0.9.3 (2021-01-28)

* Optimise `NonStreamingLexer::line_col` from *O(n*) to *O(log n)* (where *n*
  is the number of lines in the file).

* Document more clearly the constraints on what `Span`s one can safely ask a
  lexer to operate on. Note that it is always safe to use a `Span` generated
  directly by a lexer: the constraints relate to what happens if a user derives
  a `Span` themselves.

* Suppress Clippy warnings about `unnecessary_wraps`, including in code
  generated from grammar files.


# grmtools 0.9.2 (2020-11-29)

* Export the `Visibility` enum from `lrlex`.

* Ensure that lrpar rebuilds a grammar if its `visibility` is changed.


# grmtools 0.9.1 (2020-08-21)

* Fix a handful of Clippy warnings.


# grmtools 0.9.0 (2020-07-06)

## Breaking changes

* The `MF` and `Panic` recoverers (deprecated, and undocumented, since 0.4.3)
  have been removed. Please change to `RecoveryKind::CPCTPlus` (or, if you
  don't want error recovery, `RecoveryKind::None`).

## Minor changes

* The stategraph is no longer stored in the generated grammar, leading to
  useful savings in the generated binary size.


# grmtools 0.8.1 (2020-06-11)

* The modules generated for compile-time parsing by lrlex and lrpar have
  private visibility by default. Changing this previously required a manual
  alias. The `visibility` function in lrlex and lrpar's compile-time builders
  allows a different visibility to be set (e.g.
  `visibility(Visibility::Public)`. Rust has a [number of visibility
  settings](https://doc.rust-lang.org/reference/visibility-and-privacy.html#pubin-path-pubcrate-pubsuper-and-pubself)
  and the `Visibility` `enum`s in lrlex and lrpar reflect this.


# grmtools 0.8.0 (2020-05-28)

## Breaking changes

* `lrlex` now uses a `LexerDef` which all lexer definitions must `impl`. This
  means that if you want to call methods on a concrete lexer definition, you
  will almost certainly need to import `lrlex::LexerDef`. This opens the
  possibility that lrlex can seamlessly produce lexers other than
  `LRNonStreamingLexerDef`s in the future.

## Deprecations

* `lrlex::NonStreamingLexerDef` has been renamed to
  `lrlex::LRNonStreamingLexerDef`; use of the former is deprecated.

* The `lrlex::build_lex` function has been deprecated in favour of
  `LRNonStreamingLexerDef::from_str`.

## Bug fixes

* The statetable and other elements were previously included in the user binary
  with `include_bytes!`, but this could cause problems with relative path
  names. We now include the statetable and other elements in generated source
  code to avoid this issue.


# grmtools 0.7.0 (2020-04-30)

## Breaking changes

* The `Lexer` trait has been broken into two: `Lexer` and `NonStreamingLexer`.
  The former trait is now only capable of producing `Lexeme`s: the latter is
  capable of producing substrings of the input and calculating line/column
  information. This split allows the flexibility to introduce streaming lexers
  in the future (which will not be able to produce substrings of the input in
  the same way as a `NonStreamingLexer`).

  Most users will need to replace references to the `Lexer` trait
  in their code to `NonStreamingLexer`.

* `NonStreamingLexer` takes a lifetime `'input` which allows the input to last
  longer than the `NonStreamingLexer` itself. `Lexer::span_str` and
  `Lexer::span_lines_str` had the following definitions:
    ```rustc
    fn span_str(&self, span: Span) -> &str;
    fn span_lines_str(&self, span: Span) -> &str;
    ```
  As part of `NonStreamingLexer` their definitions are now:
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
  then it is likely that you need to change a type from `NonStreamingLexer` to
  `NonStreamingLexer<'input>`.


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
