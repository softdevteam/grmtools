#![allow(clippy::new_without_default)]
#![allow(clippy::type_complexity)]

use std::{error::Error, fmt, hash::Hash};

use num_traits::{PrimInt, Unsigned};
use try_from::TryFrom;

mod builder;
mod lexer;
mod parser;

use crate::parser::parse_lex;
pub use crate::{
    builder::LexerBuilder,
    lexer::{LexerDef, Rule}
};

pub type LexBuildResult<T> = Result<T, LexBuildError>;

/// Any error from the Lex parser returns an instance of this struct.
#[derive(Debug)]
pub struct LexBuildError {
    pub kind: LexErrorKind,
    line: usize,
    col: usize
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
    RegexError
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
            LexErrorKind::RegexError => s = "Invalid regular expression"
        }
        write!(f, "{} at line {} column {}", s, self.line, self.col)
    }
}

pub fn build_lex<StorageT: Copy + Eq + Hash + PrimInt + TryFrom<usize> + Unsigned>(
    s: &str
) -> Result<LexerDef<StorageT>, LexBuildError> {
    parse_lex(s)
}

/// A convenience macro for including statically compiled `.l` files. A file `src/a/b/c.l` which is
/// statically compiled by lrlex can then be used in a crate with `lrlex_mod!("a/b/c.l")`.
#[macro_export]
macro_rules! lrlex_mod {
    ($path:expr) => {
        include!(concat!(env!("OUT_DIR"), "/", $path, ".rs"));
    };
}
