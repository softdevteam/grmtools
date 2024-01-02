use super::{YaccGrammarError, YaccGrammarWarning};
use crate::{
    yacc::{parser::SpansKind, YaccGrammarErrorKind},
    NewlineCache, Span, Spanned,
};
use std::{error::Error, fmt, path, str::FromStr as _};

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

pub trait ErrorFormatter {
    fn format_error(&self, e: &YaccGrammarError) -> Box<dyn Error>;
    fn format_warning(&self, e: &YaccGrammarWarning) -> String;
}

/// Applies a `map` operation with the function `f` over
/// the error values owned by self.
pub trait ErrorMap {
    /// Applies `f` to all errors owned by self where `f` is a function
    /// returning a type that implements `Error`.
    fn format_errors<'a, F: ErrorFormatter + ?Sized>(
        &'a self,
        f: &'a F,
    ) -> impl Iterator<Item = Box<dyn Error>> + '_;
    /// Applies `f` to all warnings owned by self where `f` is a function
    /// returning a type that implements `Display`.
    fn format_warnings<'a, F: ErrorFormatter + ?Sized>(
        &'a self,
        f: &'a F,
    ) -> impl Iterator<Item = String> + '_;
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

impl ErrorMap for SimpleReport {
    fn format_errors<'a, F: ErrorFormatter + ?Sized>(
        &'a self,
        f: &'a F,
    ) -> impl Iterator<Item = Box<dyn Error>> + '_ {
        self.errors.iter().map(move |e| f.format_error(e))
    }
    fn format_warnings<'a, F: ErrorFormatter + ?Sized>(
        &'a self,
        f: &'a F,
    ) -> impl Iterator<Item = String> + '_ {
        self.warnings.iter().map(move |w| f.format_warning(w))
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

impl<R: ErrorReport + ErrorMap> ErrorMap for DedupReport<R> {
    fn format_errors<'a, F: ErrorFormatter + ?Sized>(
        &'a self,
        f: &'a F,
    ) -> impl Iterator<Item = Box<dyn Error>> + '_ {
        self.child_report.format_errors(f)
    }

    fn format_warnings<'a, F: ErrorFormatter + ?Sized>(
        &'a self,
        f: &'a F,
    ) -> impl Iterator<Item = String> + '_ {
        self.child_report.format_warnings(f)
    }
}

pub struct SimpleErrorFormatter<'a> {
    src: &'a str,
    path: &'a path::Path,
    nlc: NewlineCache,
}

impl<'a> SimpleErrorFormatter<'a> {
    #[allow(clippy::result_unit_err)]
    pub fn new(src: &'a str, path: &'a path::Path) -> Result<Self, ()> {
        Ok(Self {
            src,
            path,
            nlc: NewlineCache::from_str(src)?,
        })
    }

    fn ordinal(v: usize) -> String {
        // I didn't feel like thinking about these special cases,
        // so I just borrowed this from rusts diagnostics code.
        let suffix = match ((11..=13).contains(&(v % 100)), v % 10) {
            (false, 1) => "st",
            (false, 2) => "nd",
            (false, 3) => "rd",
            _ => "th",
        };
        format!("{v}{suffix}")
    }

    fn format_spanned(&self, e: &impl Spanned) -> String {
        let mut out = String::new();
        let path = self.path.display().to_string();
        let spans = e.spans();
        let span = spans.first().unwrap();
        let (line, col) = self
            .nlc
            .byte_to_line_num_and_col_num(self.src, span.start())
            .unwrap_or((0, 0));
        let span_src = &self.src[span.start()..span.end()];
        out.push_str(&format!("in {}:{line}:{col}: {} {}\n", path, e, span_src));
        let mut spans = e.spans().iter().enumerate().peekable();
        while let Some((span_num, span)) = spans.next() {
            let (line_start, line_end) = self.nlc.span_line_bytes(*span);
            let (line, col) = self
                .nlc
                .byte_to_line_num_and_col_num(self.src, span.start())
                .unwrap_or((0, 0));
            let (end_line, end_col) = self
                .nlc
                .byte_to_line_num_and_col_num(self.src, span.end())
                .unwrap_or((0, 0));
            out.push_str(&format!("{}| {}\n", line, &self.src[line_start..line_end]));
            if line == end_line {
                let next_line = spans
                    .peek()
                    .map(|(_, span)| span)
                    .map(|s| self.nlc.byte_to_line_num(s.start()).unwrap_or(line))
                    .unwrap_or(line);
                let dots = if next_line - line > 1 { "..." } else { "" };
                out.push_str(dots);

                // Because col is 1 indexed, subtract 1.
                out.push_str(
                    &" ".repeat(col + (line.to_string().len() + "| ".len() - dots.len()) - 1),
                );
                if span_num == 0 {
                    out.push_str(&"^".repeat(end_col - col));
                    out.push(' ');
                    out.push_str(&e.to_string());
                } else {
                    out.push_str(&"-".repeat(end_col - col));
                    out.push(' ');
                    match e.spanskind() {
                        SpansKind::DuplicationError => {
                            out.push_str(&Self::ordinal(span_num + 1));
                            out.push_str(" occurrence.");
                        }
                        SpansKind::Error => {
                            unreachable!("Should contain a single span at the site of the error")
                        }
                    }
                }
                out.push('\n');
            }
        }
        out
    }
}

impl ErrorFormatter for SimpleErrorFormatter<'_> {
    fn format_error(&self, e: &YaccGrammarError) -> Box<dyn Error> {
        self.format_spanned(e).into()
    }

    fn format_warning(&self, w: &YaccGrammarWarning) -> String {
        self.format_spanned(w)
    }
}

pub(crate) struct ReportHandler<'a, T> {
    any_errors_found: bool,
    report: &'a mut T,
}

impl<'a, R: ErrorReport> ReportHandler<'a, R> {
    pub(crate) fn new(report: &'a mut R) -> Self {
        ReportHandler {
            report,
            any_errors_found: false,
        }
    }

    pub(crate) fn finish(&mut self) {
        self.report.finish()
    }

    /// `From<YaccGrammarError> for ASTBuilderError` is
    /// intentionally not derived. This will submit the error to an `ErrorReport`
    /// and note that errors were found then return a `ConstructionFailure`.
    pub(crate) fn error<T>(
        &mut self,
        result: Result<T, YaccGrammarError>,
    ) -> Result<T, ASTBuilderError> {
        match result {
            Ok(x) => Ok(x),
            Err(e) => {
                self.any_errors_found = true;
                self.report.grammar_error(e);
                Err(ASTBuilderError::ConstructionFailure)
            }
        }
    }

    /// For errors which are non-fatal where the parsing process can continue.
    /// This will submit the error to a report, and note that errors were found.
    pub(crate) fn non_fatal_error(&mut self, e: YaccGrammarError) {
        self.any_errors_found = true;
        self.report.grammar_error(e)
    }

    pub(crate) fn warning(&mut self, e: YaccGrammarWarning) {
        self.report.grammar_warning(e)
    }
    /// Return whether any errors were found including non-fatal errors.
    pub(crate) fn any_errors_found(&self) -> bool {
        self.any_errors_found
    }
}

#[derive(Debug)]
pub enum ASTBuilderError {
    /// This error is just an indication that a failure occurred.
    /// But otherwise lacks information such as what and where.
    /// For that you will need to look at a `YaccGrammarError`
    /// in an `ErrorReport`.
    ConstructionFailure,
    MissingSource,
    MissingErrorReport,
    MissingYaccKind,
}

impl fmt::Display for ASTBuilderError {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            Self::ConstructionFailure => write!(f, "Grammar construction failure"),
            Self::MissingSource => write!(f, "Sources for a grammar was not given"),
            Self::MissingYaccKind => write!(f, "`YaccKind` for a grammar was not specified"),
            Self::MissingErrorReport => write!(f, "`ErrorReport` for grammar was not given"),
        }
    }
}
