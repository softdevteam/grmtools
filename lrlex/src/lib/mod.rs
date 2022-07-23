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

use std::{error::Error, fmt};

mod ctbuilder;
#[doc(hidden)]
pub mod lexemes;
mod lexer;
mod parser;

#[allow(deprecated)]
pub use crate::ctbuilder::LexerBuilder;
pub use crate::{
    ctbuilder::{ct_token_map, CTLexer, CTLexerBuilder, LexerKind, Visibility},
    lexemes::DefaultLexeme,
    lexer::{LRNonStreamingLexer, LRNonStreamingLexerDef, LexerDef, Rule},
    parser::StartState,
};

use cfgrammar::Span;

pub type LexBuildResult<T> = Result<T, Vec<LexBuildError>>;

/// Any error from the Lex parser returns an instance of this struct.
#[derive(Debug)]
pub struct LexBuildError {
    pub kind: LexErrorKind,
    pub span: Span,
}

impl Error for LexBuildError {}

/// The various different possible Lex parser errors.
#[derive(Debug)]
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
    DuplicateName(Vec<Span>),
    RegexError,
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
            LexErrorKind::DuplicateName(_) => "Rule name already exists",
            LexErrorKind::RegexError => "Invalid regular expression",
        };
        write!(f, "{s}")
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
