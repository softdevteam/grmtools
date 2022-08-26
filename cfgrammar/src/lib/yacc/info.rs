use crate::yacc::{YaccGrammarError, YaccGrammarWarning};

/// Controls the collection of and collects information about warnings and other information
/// that result during the construction of a `YaccGrammar`.  If `warnings_as_errors` is `true`
/// does not collect any warnings.
pub struct YaccGrammarInfo {
    pub(crate) warnings_as_errors: bool,
    warnings: Vec<YaccGrammarWarning>,
}

impl YaccGrammarInfo {
    pub fn new(warnings_as_errors: bool) -> Self {
        YaccGrammarInfo {
            warnings_as_errors,
            warnings: Vec::new(),
        }
    }

    /// If `warnings_as_errors` is `true` converts the warning to an error and returns `Some`.
    /// Otherwise adds the warning for later usage and returns `None`.
    pub(crate) fn add_warning(&mut self, warning: YaccGrammarWarning) -> Option<YaccGrammarError> {
        if self.warnings_as_errors {
            Some(YaccGrammarError::from(warning))
        } else {
            self.warnings.push(warning);
            None
        }
    }

    /// If `self.warnings_as_errors` is `true` returns an empty slice.
    /// Otherwise return the list of warnings collected during grammar
    /// construction.
    pub fn warnings(&self) -> &[YaccGrammarWarning] {
        self.warnings.as_slice()
    }
}
