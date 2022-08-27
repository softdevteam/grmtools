use crate::yacc::{YaccGrammarError, YaccGrammarWarning};

/// Controls the collection of and collects information about warnings and other information
/// that result during the construction of a `YaccGrammar`.  If `warnings_as_errors` is `true`
/// does not collect any warnings.
pub struct YaccGrammarInfo {
    pub(crate) warnings_as_errors: bool,
    warnings: Vec<YaccGrammarWarning>,
}

#[derive(Default)]
pub struct YaccGrammarInfoBuilder {
    warnings_as_errors: bool,
}

impl YaccGrammarInfoBuilder {
    pub fn warnings_as_errors(mut self) -> Self {
        self.warnings_as_errors = true;
        self
    }

    pub fn build(self) -> YaccGrammarInfo {
        YaccGrammarInfo {
            warnings_as_errors: self.warnings_as_errors,
            warnings: Vec::new(),
        }
    }
}

impl YaccGrammarInfo {
    /// Returns a `YaccGrammarInfoBuilder` for configuring the behavior of a `YaccGrammarInfo`
    pub fn builder() -> YaccGrammarInfoBuilder {
        Default::default()
    }

    /// Returns a `YaccGrammarInfo` settings that are enabled are selected with a disposition
    /// towards caution. For example, the treatment of warnings as errors would be enabled.
    ///
    /// The exact set of flags enabled by this function are not specified and subject to change.
    pub fn cautious() -> Self {
        Self::builder().warnings_as_errors().build()
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
