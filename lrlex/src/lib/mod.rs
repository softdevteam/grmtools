//! `lrlex` is a partial replacement for [`lex`](http://dinosaur.compilertools.net/lex/index.html)
//! / [`flex`](https://westes.github.io/flex/manual/). It takes in a `.l` file and statically
//! compiles it to Rust code. The resulting [LRNonStreamingLexerDef] can then be given an input
//! string, from which it instantiates an [LRNonStreamingLexer]. This provides an iterator which
//! can produce the sequence of [lrpar::Lexeme]s for that input, as well as answer basic queries
//! about [lrpar::Span]s (e.g. extracting substrings, calculating line and column numbers).

#![allow(clippy::new_without_default)]
#![allow(clippy::type_complexity)]

use std::{error::Error, fmt, hash::Hash};

use num_traits::{PrimInt, Unsigned};
use try_from::TryFrom;

mod builder;
mod lexer;
mod parser;

pub use crate::{
    builder::{LexerBuilder, LexerKind},
    lexer::{LRNonStreamingLexer, LRNonStreamingLexerDef, LexerDef, Rule},
};

pub type LexBuildResult<T> = Result<T, LexBuildError>;

/// Any error from the Lex parser returns an instance of this struct.
#[derive(Debug)]
pub struct LexBuildError {
    pub kind: LexErrorKind,
    line: usize,
    col: usize,
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
    DuplicateName,
    RegexError,
}

impl fmt::Display for LexBuildError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let s;
        match self.kind {
            LexErrorKind::PrematureEnd => s = "File ends prematurely",
            LexErrorKind::RoutinesNotSupported => s = "Routines not currently supported",
            LexErrorKind::UnknownDeclaration => s = "Unknown declaration",
            LexErrorKind::MissingSpace => s = "Rule is missing a space",
            LexErrorKind::InvalidName => s = "Invalid rule name",
            LexErrorKind::DuplicateName => s = "Rule name already exists",
            LexErrorKind::RegexError => s = "Invalid regular expression",
        }
        write!(f, "{} at line {} column {}", s, self.line, self.col)
    }
}

#[deprecated(since = "0.8.0", note = "Please use LRNonStreamingLexerDef::from_str")]
pub fn build_lex<StorageT: Copy + Eq + Hash + PrimInt + TryFrom<usize> + Unsigned>(
    s: &str,
) -> Result<LRNonStreamingLexerDef<StorageT>, LexBuildError> {
    LRNonStreamingLexerDef::from_str(s)
}

#[deprecated(
    since = "0.8.0",
    note = "This struct has been renamed to LRNonStreamingLexerDef"
)]
pub type NonStreamingLexerDef<StorageT> = LRNonStreamingLexerDef<StorageT>;

/// A convenience macro for including statically compiled `.l` files. A file `src/a/b/c.l` which is
/// statically compiled by lrlex can then be used in a crate with `lrlex_mod!("a/b/c.l")`.
#[macro_export]
macro_rules! lrlex_mod {
    ($path:expr) => {
        include!(concat!(env!("OUT_DIR"), "/", $path, ".rs"));
    };
}
