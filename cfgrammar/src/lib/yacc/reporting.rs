use super::{YaccGrammarError, YaccGrammarWarning};
use crate::{
    yacc::{parser::SpansKind, YaccGrammarErrorKind},
    Span, Spanned,
};
use std::fmt;

/// Caller gives ownership of errors and warnings to the impl.
pub trait ErrorReport {
    /// Gives ownership of an error to self.
    fn grammar_error(&mut self, err: YaccGrammarError);
    /// Gives ownership of a warning to self.
    fn grammar_warning(&mut self, err: YaccGrammarWarning);

    /// Default implementation does nothing. If you override this
    /// and have a child report you must call finish on the child.
    ///
    /// Some `ErrorReport` implementations may wrap others,
    /// and buffer the errors passed in. This function allows
    /// them to drain that buffer.
    ///
    /// Another use case is when an `ErrorReport` containing
    /// an `mpsc::Sender`, this would be called to drop the
    /// `Sender`, so an `mpsc::Receiver` won't block forever
    /// after the last error has been sent.
    ///
    /// This function is called at the end of `ASTBuilder::build`.
    ///
    /// Thoughts:
    /// Waiting until we are finished is overzealous, we *know*
    /// we only find certain errors in sections, and won't find
    /// duplicates in later sections. Thus we could generalize this.
    /// to something like:
    /// ```
    /// enum Stage {
    ///   Header,
    ///   Rules,
    ///   Program,
    ///   Finished,
    /// }
    /// fn stage(stage: Stage) {}
    ///
    /// ```
    /// fn stage()
    fn finish(&mut self) {}
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

pub struct DedupReport<R: ErrorReport> {
    errors: Vec<YaccGrammarError>,
    child_report: R,
}

impl<R: ErrorReport> DedupReport<R> {
    pub fn new(r: R) -> Self {
        Self {
            errors: Vec::new(),
            child_report: r,
        }
    }
    pub fn child(&self) -> &R {
        &self.child_report
    }
}

impl<R: ErrorReport> ErrorReport for DedupReport<R> {
    fn grammar_error(&mut self, err: YaccGrammarError) {
        // We would need to make a few things pub (kind) to implement this outside of the crate.
        fn add_duplicate_occurrence(
            errs: &mut Vec<YaccGrammarError>,
            kind: YaccGrammarErrorKind,
            orig_span: Span,
            dup_span: Span,
        ) {
            // .rev() might be better when we hit.
            if !errs.iter_mut().any(|e| {
                if e.kind == kind && e.spans[0] == orig_span {
                    e.spans.push(dup_span);
                    true
                } else {
                    false
                }
            }) {
                errs.push(YaccGrammarError {
                    kind,
                    spans: vec![orig_span, dup_span],
                });
            }
        }
        let spans = err.spans();
        if let SpansKind::DuplicationError = err.spanskind() {
            add_duplicate_occurrence(&mut self.errors, err.kind.clone(), spans[0], spans[1])
        } else {
            // Rather than send directly to the child report
            // We store them to maintain their order.
            self.errors.push(err);
        }
    }
    fn grammar_warning(&mut self, w: YaccGrammarWarning) {
        // Currently there is no such thing as a duplicate warning.
        self.child_report.grammar_warning(w);
    }

    fn finish(&mut self) {
        for e in self.errors.drain(..) {
            self.child_report.grammar_error(e);
        }
        self.child_report.finish();
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
