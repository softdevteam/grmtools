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
    /// Returns all the warnings collected during grammar construction.
    pub fn warnings(&self) -> &[YaccGrammarWarning] {
        self.warnings.as_slice()
    }
}
