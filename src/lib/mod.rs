use std::fmt;

pub mod grammar;
pub mod yacc;

pub mod pgen;
pub use grammar::{Grammar, GrammarError};
pub use self::yacc::{YaccError, YaccErrorKind};
use self::yacc::parse_yacc;

#[derive(Debug)]
pub enum FromYaccError {
    YaccError(YaccError),
    GrammarError(GrammarError)
}

impl From<YaccError> for FromYaccError {
    fn from(err: YaccError) -> FromYaccError {
        FromYaccError::YaccError(err)
    }
}

impl From<GrammarError> for FromYaccError {
    fn from(err: GrammarError) -> FromYaccError {
        FromYaccError::GrammarError(err)
    }
}

impl fmt::Display for FromYaccError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            FromYaccError::YaccError(ref e) => e.fmt(f),
            FromYaccError::GrammarError(ref e) => e.fmt(f),
        }
    }
}

pub fn from_yacc(s:&String) -> Result<Grammar, FromYaccError> {
    let grm = try!(parse_yacc(s));
    if let Some(e) = grm.validate() { return Err(FromYaccError::GrammarError(e)); }
    Ok(grm)
}
