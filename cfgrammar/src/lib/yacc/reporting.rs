use super::{YaccGrammarError, YaccGrammarWarning};
use std::fmt;

/// Caller gives ownership of errors and warnings to the impl.
pub trait ErrorReport {
    /// Gives ownership of an error to self.
    fn grammar_error(&mut self, err: YaccGrammarError);
    /// Gives ownership of a warning to self.
    fn grammar_warning(&mut self, err: YaccGrammarWarning);
}

/// A basic Report that stores errors and warnings in a `Vec`.
pub struct SimpleReport {
    errors: Vec<YaccGrammarError>,
    warnings: Vec<YaccGrammarWarning>,
}

impl ErrorReport for SimpleReport {
    fn grammar_error(&mut self, err: YaccGrammarError) {
        self.errors.push(err);
    }
    fn grammar_warning(&mut self, err: YaccGrammarWarning) {
        self.warnings.push(err);
    }
}

impl SimpleReport {
    pub fn new() -> Self {
        SimpleReport {
            errors: vec![],
            warnings: vec![],
        }
    }
    pub(crate) fn warnings(&self) -> &[YaccGrammarWarning] {
        &self.warnings
    }
    pub(crate) fn errors(&self) -> &[YaccGrammarError] {
        &self.errors
    }
}
#[derive(Debug)]
pub enum ASTBuilderError {
    /// This error is just an indication that a failure occurred.
    /// But otherwise lacks information such as what and where.
    /// For that you will need to look at a `YaccGrammarError`
    /// in an `ErrorReport`.
    ConstructionFailure,
}

impl fmt::Display for ASTBuilderError {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            Self::ConstructionFailure => write!(f, "Grammar construction failure"),
        }
    }
}
