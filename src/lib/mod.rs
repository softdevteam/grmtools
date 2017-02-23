use std::fmt;

#[macro_use] extern crate lazy_static;
#[macro_use] extern crate custom_derive;
#[macro_use] extern crate newtype_derive;


mod ast;
pub mod grammar;
mod yacc_parser;
mod stategraph;
pub mod statetable;

pub use grammar::{Grammar, PIdx, RIdx, Symbol, TIdx};
pub use ast::{GrammarAST, GrammarValidationError};
use stategraph::StateGraph;
pub use statetable::{Action, StateTable};
pub use yacc_parser::{YaccParserError, YaccParserErrorKind};
use yacc_parser::parse_yacc;

#[derive(Debug)]
pub enum YaccToStateTableError {
    YaccParserError(YaccParserError),
    GrammarValidationError(GrammarValidationError)
}

impl From<YaccParserError> for YaccToStateTableError {
    fn from(err: YaccParserError) -> YaccToStateTableError {
        YaccToStateTableError::YaccParserError(err)
    }
}

impl From<GrammarValidationError> for YaccToStateTableError {
    fn from(err: GrammarValidationError) -> YaccToStateTableError {
        YaccToStateTableError::GrammarValidationError(err)
    }
}

impl fmt::Display for YaccToStateTableError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            YaccToStateTableError::YaccParserError(ref e) => e.fmt(f),
            YaccToStateTableError::GrammarValidationError(ref e) => e.fmt(f),
        }
    }
}

pub fn yacc_to_statetable(s: &str) -> Result<(Grammar, StateTable), YaccToStateTableError> {
    let ast = try!(parse_yacc(s));
    try!(ast.validate());
    let grm = Grammar::new(&ast);
    let sg = StateGraph::new(&grm);
    let st = StateTable::new(&grm, &sg);
    Ok((grm, st))
}
