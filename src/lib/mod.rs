use std::fmt;

#[macro_use]
extern crate lazy_static;

pub mod grammar;
pub mod grammar_ast;
pub mod yacc;
pub mod stategraph;
pub mod statetable;

pub use grammar::ast_to_grammar;
pub use grammar_ast::{GrammarAST, GrammarASTError};
pub use self::yacc::{YaccError, YaccErrorKind};
use self::yacc::parse_yacc;

#[derive(Debug)]
pub enum FromYaccError {
    YaccError(YaccError),
    GrammarASTError(GrammarASTError)
}

impl From<YaccError> for FromYaccError {
    fn from(err: YaccError) -> FromYaccError {
        FromYaccError::YaccError(err)
    }
}

impl From<GrammarASTError> for FromYaccError {
    fn from(err: GrammarASTError) -> FromYaccError {
        FromYaccError::GrammarASTError(err)
    }
}

impl fmt::Display for FromYaccError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            FromYaccError::YaccError(ref e) => e.fmt(f),
            FromYaccError::GrammarASTError(ref e) => e.fmt(f),
        }
    }
}

pub fn from_yacc(s: &str) -> Result<GrammarAST, FromYaccError> {
    let grmast = try!(parse_yacc(s));
    try!(grmast.validate());
    Ok(grmast)
}
