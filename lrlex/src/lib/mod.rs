//! `lrlex` is a partial replacement for [`lex`](http://dinosaur.compilertools.net/lex/index.html)
//! / [`flex`](https://westes.github.io/flex/manual/). It takes in a `.l` file and statically
//! compiles it to Rust code. The resulting [LRNonStreamingLexerDef] can then be given an input
//! string, from which it instantiates an [LRNonStreamingLexer]. This provides an iterator which
//! can produce the sequence of [lrpar::Lexeme]s for that input, as well as answer basic queries
//! about [cfgrammar::Span]s (e.g. extracting substrings, calculating line and column numbers).

#![allow(clippy::new_without_default)]
#![allow(clippy::type_complexity)]
#![allow(clippy::unnecessary_wraps)]
#![allow(clippy::upper_case_acronyms)]
#![forbid(unsafe_code)]
#![deny(unreachable_pub)]

use std::{error::Error, fmt};

mod ctbuilder;
#[doc(hidden)]
pub mod defaults;
mod lexer;
mod parser;

pub use crate::{
    ctbuilder::{ct_token_map, CTLexer, CTLexerBuilder, LexerKind, RustEdition, Visibility},
    defaults::{DefaultLexeme, DefaultLexerTypes},
    lexer::{
        LRNonStreamingLexer, LRNonStreamingLexerDef, LexFlags, LexerDef, Rule, DEFAULT_LEX_FLAGS,
        UNSPECIFIED_LEX_FLAGS,
    },
    parser::StartState,
    parser::StartStateOperation,
};

use cfgrammar::yacc::parser::SpansKind;
use cfgrammar::{Span, Spanned};

pub type LexBuildResult<T> = Result<T, Vec<LexBuildError>>;

/// Any error from the Lex parser returns an instance of this struct.
#[derive(Debug)]
pub struct LexBuildError {
    pub(crate) kind: LexErrorKind,
    pub(crate) spans: Vec<Span>,
}

impl Error for LexBuildError {}

/// The various different possible Lex parser errors.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum LexErrorKind {
    PrematureEnd,
    RoutinesNotSupported,
    UnknownDeclaration,
    MissingSpace,
    InvalidName,
    UnknownStartState,
    DuplicateStartState,
    InvalidStartState,
    InvalidStartStateName,
    DuplicateName,
    RegexError,
    VerbatimNotSupported,
}

impl Spanned for LexBuildError {
    fn spans(&self) -> &[Span] {
        self.spans.as_slice()
    }

    fn spanskind(&self) -> SpansKind {
        match self.kind {
            LexErrorKind::PrematureEnd
            | LexErrorKind::RoutinesNotSupported
            | LexErrorKind::UnknownDeclaration
            | LexErrorKind::MissingSpace
            | LexErrorKind::InvalidName
            | LexErrorKind::UnknownStartState
            | LexErrorKind::InvalidStartState
            | LexErrorKind::InvalidStartStateName
            | LexErrorKind::VerbatimNotSupported
            | LexErrorKind::RegexError => SpansKind::Error,
            LexErrorKind::DuplicateName | LexErrorKind::DuplicateStartState => {
                SpansKind::DuplicationError
            }
        }
    }
}

impl fmt::Display for LexBuildError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let s = match self.kind {
            LexErrorKind::VerbatimNotSupported => "Verbatim code not supported",
            LexErrorKind::PrematureEnd => "File ends prematurely",
            LexErrorKind::RoutinesNotSupported => "Routines not currently supported",
            LexErrorKind::UnknownDeclaration => "Unknown declaration",
            LexErrorKind::MissingSpace => "Rule is missing a space",
            LexErrorKind::InvalidName => "Invalid rule name",
            LexErrorKind::UnknownStartState => "Start state not known",
            LexErrorKind::DuplicateStartState => "Start state already exists",
            LexErrorKind::InvalidStartState => "Invalid start state",
            LexErrorKind::InvalidStartStateName => "Invalid start state name",
            LexErrorKind::DuplicateName => "Rule name already exists",
            LexErrorKind::RegexError => "Invalid regular expression",
        };
        write!(f, "{s}")
    }
}

#[derive(Copy, Clone, Debug)]
pub struct StartStateId {
    _id: usize,
}

impl StartStateId {
    fn new(id: usize) -> Self {
        Self { _id: id }
    }
}

/// A Lexing error.
#[derive(Clone, Debug)]
pub struct LRLexError {
    span: Span,
    lexing_state: Option<StartStateId>,
}

impl lrpar::LexError for LRLexError {
    fn span(&self) -> Span {
        self.span
    }
}

impl LRLexError {
    /// Construct a new LRLex error covering `span`.
    pub fn new(span: Span) -> Self {
        LRLexError {
            span,
            lexing_state: None,
        }
    }

    /// Construct a new LRLex error covering `span` for `lexing_state`.
    pub fn new_with_lexing_state(span: Span, lexing_state: StartStateId) -> Self {
        LRLexError {
            span,
            lexing_state: Some(lexing_state),
        }
    }

    /// Returns the state, if there was one, that the lexer was in when the error was detected.
    pub fn lexing_state(&self) -> Option<StartStateId> {
        self.lexing_state
    }
}

impl Error for LRLexError {}

impl fmt::Display for LRLexError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "Couldn't lex input starting at byte {}",
            self.span.start()
        )
    }
}

#[deprecated(
    since = "0.8.0",
    note = "This struct has been renamed to LRNonStreamingLexerDef"
)]
pub type NonStreamingLexerDef<StorageT> = LRNonStreamingLexerDef<StorageT>;

/// A convenience macro for including statically compiled `.l` files. A file `src/a/b/c.l`
/// processed by [CTLexerBuilder::lexer_in_src_dir] can then be used in a crate with
/// `lrlex_mod!("a/b/c.l")`.
///
/// Note that you can use `lrlex_mod` with [CTLexerBuilder::output_path] if, and only if, the
/// output file was placed in [std::env::var]`("OUT_DIR")` or one of its subdirectories.
#[macro_export]
macro_rules! lrlex_mod {
    ($path:expr) => {
        include!(concat!(env!("OUT_DIR"), "/", $path, ".rs"));
    };
}

/// This private module with pub items which is directly related to
/// the "Sealed trait" pattern. These items are used within the current
/// crate. See `unstable_api` module for enabling usage outside the crate.
mod unstable {
    #![allow(unused)]
    #![allow(unreachable_pub)]
    pub struct UnstableApi;
    pub trait UnstableTrait {}
}

/// A module for lifting restrictions on visibility by enabling unstable features.
///
/// See the sources for a complete list of features, and members.
pub mod unstable_api {
    /// Unstable functions that take a value `UnstableApi` require
    /// the "_unstable_api" feature. This feature controls
    /// whether the value has `pub` visibility outside the crate.
    #[cfg(feature = "_unstable_api")]
    pub use crate::unstable::UnstableApi;

    /// This is a a supertrait for traits that are considered to be Unstable.
    /// Unstable traits do not provide any semver guarantees.
    ///
    /// Enabling the `_unsealed_unstable traits` makes this supertrait publicly
    /// Visible.
    ///
    ///
    /// Declaring an unstable Api within the crate:
    /// ```ignore_rust
    /// // Within the crate use `crate::unstable::` .
    /// pub trait Foo: crate::unstable::UnstableTrait {
    ///     fn foo(key: crate::unstable::UnstableApi);
    /// }
    /// ```
    ///
    /// Deriving the trait outside the crate (requires feature `_unsealed_unstable_traits`)
    /// ```ignore_rust
    /// struct Bar;
    /// impl unstable_api::UnstableTrait for Bar{}
    /// impl Foo for Bar {
    ///   fn foo(key: unstable_api::UnstableApi) {
    ///     ...
    ///   }
    /// }
    /// ```
    ///
    ///
    /// Calling an implementation of the trait outside the crate (requires feature `_unstable_api`:
    /// ```ignore_rust
    ///   let x: &dyn Foo = ...;
    ///   x.foo(unstable_api::UnstableApi);
    /// ```
    #[cfg(feature = "_unsealed_unstable_traits")]
    pub use crate::unstable::UnstableTrait;

    /// An value that acts as a key to inform callers that they are
    /// calling an unstable internal api. This value is public by default.
    /// Access to it does not require any features to be enabled.
    ///
    /// Q. When this should be used?
    ///
    /// A. When generated code needs to call internal api within it,
    /// where you do not want the caller to have to enable any features
    /// to use the generated code.
    pub struct InternalPublicApi;
}
