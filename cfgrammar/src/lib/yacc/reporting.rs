use super::{YaccGrammarError, YaccGrammarWarning};

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
