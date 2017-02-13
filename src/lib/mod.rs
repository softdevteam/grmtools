use std::fmt;

#[macro_use]
extern crate lazy_static;

pub mod grammar;
mod grammar_ast;
mod yacc_parser;
mod stategraph;
pub mod statetable;

pub use grammar::{Grammar, RIdx, Symbol};
pub use grammar_ast::{GrammarAST, GrammarASTError};
use stategraph::StateGraph;
pub use statetable::{Action, StateTable};
pub use yacc_parser::{YaccParserError, YaccParserErrorKind};
use yacc_parser::parse_yacc;

#[derive(Debug)]
pub enum FromYaccParserError {
    YaccParserError(YaccParserError),
    GrammarASTError(GrammarASTError)
}

impl From<YaccParserError> for FromYaccParserError {
    fn from(err: YaccParserError) -> FromYaccParserError {
        FromYaccParserError::YaccParserError(err)
    }
}

impl From<GrammarASTError> for FromYaccParserError {
    fn from(err: GrammarASTError) -> FromYaccParserError {
        FromYaccParserError::GrammarASTError(err)
    }
}

impl fmt::Display for FromYaccParserError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            FromYaccParserError::YaccParserError(ref e) => e.fmt(f),
            FromYaccParserError::GrammarASTError(ref e) => e.fmt(f),
        }
    }
}

pub fn yacc_to_statetable(s: &str) -> Result<(Grammar, StateTable), FromYaccParserError> {
    let ast = try!(parse_yacc(s));
    try!(ast.validate());
    let grm = Grammar::new(&ast);
    let sg = StateGraph::new(&grm);
    let st = StateTable::new(&grm, &sg);
    Ok((grm, st))
}
