extern crate regex;

use std::fmt;

pub mod ast;
mod lexer;
mod parser;

use ast::LexAST;
use lexer::{lex, Lexeme, LexError};
use parser::parse_lex;

#[macro_use]
extern crate lazy_static;

pub type LexBuildResult<T> = Result<T, LexBuildError>;

/// Any error from the Lex parser returns an instance of this struct.
#[derive(Debug)]
pub struct LexBuildError {
    pub kind: LexErrorKind,
    line: usize,
    col: usize
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

pub fn build_lex(s: &str) -> Result<LexAST, LexBuildError> {
    parse_lex(s)
}

pub fn do_lex(ast: &LexAST, s: &str) -> Result<Vec<Lexeme>, LexError> {
    lex(&ast, s)
}
