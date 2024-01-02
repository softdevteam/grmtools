use super::{YaccGrammarError, YaccGrammarWarning};

/// Caller gives ownership of errors and warnings to the impl.
pub trait ErrorReport {
    /// Gives ownership of an error to self.
    fn grammar_error(&mut self, err: YaccGrammarError);
    /// Gives ownership of a warning to self.
    fn grammar_warning(&mut self, err: YaccGrammarWarning);
}