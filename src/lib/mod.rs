use std::fmt;

#[macro_use]
extern crate lazy_static;

pub mod grammar;
mod grammar_ast;
mod yacc;
mod stategraph;
pub mod statetable;

pub use grammar::{ast_to_grammar, Grammar, RIdx, Symbol};
pub use grammar_ast::{GrammarAST, GrammarASTError};
use stategraph::StateGraph;
pub use statetable::{Action, StateTable};
pub use yacc::{YaccError, YaccErrorKind};
use yacc::parse_yacc;

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

pub fn yacc_to_statetable(s: &str) -> Result<(Grammar, StateTable), FromYaccError> {
    let ast = try!(parse_yacc(s));
    try!(ast.validate());
    let grm = ast_to_grammar(&ast);
    let sg = StateGraph::new(&grm);
    let st = StateTable::new(&grm, &sg);
    Ok((grm, st))
}
