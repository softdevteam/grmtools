// Copyright (c) 2017 King's College London
// created by the Software Development Team <http://soft-dev.org/>
//
// The Universal Permissive License (UPL), Version 1.0
//
// Subject to the condition set forth below, permission is hereby granted to any person obtaining a
// copy of this software, associated documentation and/or data (collectively the "Software"), free
// of charge and under any and all copyright rights in the Software, and any and all patent rights
// owned or freely licensable by each licensor hereunder covering either (i) the unmodified
// Software as contributed to or provided by such licensor, or (ii) the Larger Works (as defined
// below), to deal in both
//
// (a) the Software, and
// (b) any piece of software and/or hardware listed in the lrgrwrks.txt file
// if one is included with the Software (each a "Larger Work" to which the Software is contributed
// by such licensors),
//
// without restriction, including without limitation the rights to copy, create derivative works
// of, display, perform, and distribute the Software and make, use, sell, offer for sale, import,
// export, have made, and have sold the Software and the Larger Work(s), and to sublicense the
// foregoing rights on either these or other terms.
//
// This license is subject to the following condition: The above copyright notice and either this
// complete permission notice or at a minimum a reference to the UPL must be included in all copies
// or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING
// BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
// NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
// DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

#![feature(fs_read_write)]
#![feature(try_from)]

extern crate filetime;
extern crate regex;
extern crate typename;

use std::convert::TryFrom;
use std::error::Error;
use std::fmt;

mod builder;
mod lexer;
mod parser;

pub use builder::{process_file, process_file_in_src};
pub use lexer::{Lexeme, LexerDef, Lexer, Rule};
use parser::parse_lex;

pub type LexBuildResult<T> = Result<T, LexBuildError>;

/// Any error from the Lex parser returns an instance of this struct.
#[derive(Debug)]
pub struct LexBuildError {
    pub kind: LexErrorKind,
    line: usize,
    col: usize
}

impl Error for LexBuildError {
    fn description(&self) -> &str {
        panic!("XXX");
    }

    fn cause(&self) -> Option<&Error> {
        None
    }
}

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
            LexErrorKind::PrematureEnd         => s = "File ends prematurely",
            LexErrorKind::RoutinesNotSupported => s = "Routines not currently supported",
            LexErrorKind::UnknownDeclaration   => s = "Unknown declaration",
            LexErrorKind::MissingSpace         => s = "Rule is missing a space",
            LexErrorKind::InvalidName          => s = "Invalid rule name",
            LexErrorKind::DuplicateName        => s = "Rule name already exists",
            LexErrorKind::RegexError           => s = "Invalid regular expression"
        }
        write!(f, "{} at line {} column {}", s, self.line, self.col)
    }
}

pub fn build_lex<TokId: Copy + Eq + TryFrom<usize>>(s: &str) -> Result<LexerDef<TokId>, LexBuildError> {
    parse_lex(s)
}

/// A convenience macro for including statically compiled `.l` files. A file `src/x.l` which is
/// statically compiled by lrlex can then be used in a crate with `lrlex_mod!(x)`.
#[macro_export]
macro_rules! lrlex_mod {
    ($n:ident) => { include!(concat!(env!("OUT_DIR"), "/", stringify!($n), ".rs")); };
}
