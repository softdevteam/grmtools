// Copyright (c) 2017 King's College London
// created by the Software Development Team <http://soft-dev.org/>
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0>, or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, or the UPL-1.0 license <http://opensource.org/licenses/UPL>
// at your option. This file may not be copied, modified, or distributed except according to those
// terms.

#[macro_use]
extern crate lazy_static;
extern crate lrpar;
extern crate num_traits;
extern crate regex;
extern crate try_from;
extern crate typename;

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

/// A convenience macro for including statically compiled `.l` files. A file `src/x.l` which is
/// statically compiled by lrlex can then be used in a crate with `lrlex_mod!(x)`.
#[macro_export]
macro_rules! lrlex_mod {
    ($n:ident) => {
        include!(concat!(env!("OUT_DIR"), "/", stringify!($n), ".rs"));
    };
}
