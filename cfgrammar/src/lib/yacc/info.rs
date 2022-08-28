use crate::yacc::YaccGrammarWarning;

/// Collects information about warnings which occur
/// during the construction of a `YaccGrammar`.
pub struct YaccGrammarInfo {
    pub(crate) warnings: Vec<YaccGrammarWarning>,
}

impl YaccGrammarInfo {
    pub fn new() -> YaccGrammarInfo {
        YaccGrammarInfo {
            warnings: Vec::new(),
        }
    }
    /// If `self.warnings_as_errors` is `true` returns an empty slice.
    /// Otherwise return the list of warnings collected during grammar
    /// construction.
    pub fn warnings(&self) -> &[YaccGrammarWarning] {
        self.warnings.as_slice()
    }
}
