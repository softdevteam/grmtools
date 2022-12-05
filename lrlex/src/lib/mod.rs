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

use std::{error::Error, fmt};

mod ctbuilder;
#[doc(hidden)]
pub mod lexemes;
mod lexer;
mod parser;

pub use crate::{
    ctbuilder::{ct_token_map, CTLexer, CTLexerBuilder, LexerKind, RustEdition, Visibility},
    lexemes::DefaultLexeme,
    lexer::{LRNonStreamingLexer, LRNonStreamingLexerDef, LexerDef, Rule},
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
pub type NonStreamingLexerDef<LexemeT, StorageT> = LRNonStreamingLexerDef<LexemeT, StorageT>;

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
