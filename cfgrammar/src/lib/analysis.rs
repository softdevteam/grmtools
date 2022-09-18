use crate::yacc::ast::{GrammarAST, Symbol};
use crate::yacc::{YaccGrammarWarning, YaccGrammarWarningKind};
use std::ops::Deref;

/// Performs an analysis on a given `Subject`, the given
/// subject may be known to have pre-existing errors.
pub trait Analysis<Subject> {
    /// Perform an analysis on a given subject The mechanisms by which you retrieve the
    /// results of an analysis are not specified by the trait, and particular to the types
    /// that implement the trait.
    fn analyse(&mut self, subject: &Subject);
}

pub struct YaccGrammarWarningAnalysis<SourceId>
where
    SourceId: PartialEq + ToOwned + ?Sized,
{
    src_id: SourceId::Owned,
    warnings: Vec<YaccGrammarWarning>,
}

impl<SourceId: PartialEq + ToOwned + ?Sized> YaccGrammarWarningAnalysis<SourceId> {
    /// Create a new analysis given a SourceId such as the filename of a yacc file
    /// For example, `YaccGrammarWarningAnalysis::new("foo.y")`
    pub fn new(src_id: &SourceId) -> Self {
        Self {
            src_id: src_id.to_owned(),
            warnings: Vec::new(),
        }
    }
    pub fn source_id(&self) -> &SourceId::Owned {
        &self.src_id
    }
}

impl<SourceId: PartialEq + ToOwned + ?Sized> Deref for YaccGrammarWarningAnalysis<SourceId> {
    type Target = Vec<YaccGrammarWarning>;

    fn deref(&self) -> &Self::Target {
        &self.warnings
    }
}

/// For the results, this `Analysis` can be dereferenced into a Boxed slice of `YaccGrammarWarnings`.
impl<SourceId: PartialEq + ToOwned + ?Sized> Analysis<GrammarAST>
    for YaccGrammarWarningAnalysis<SourceId>
{
    fn analyse(&mut self, ast: &GrammarAST) {
        self.warnings.extend(ast.unused_symbols().map(|sym_idx| {
            let symbol = sym_idx.symbol(ast);
            let (kind, span) = match symbol {
                Symbol::Token(_, span) => (YaccGrammarWarningKind::UnusedToken, span),
                Symbol::Rule(_, span) => (YaccGrammarWarningKind::UnusedRule, span),
            };
            YaccGrammarWarning {
                kind,
                spans: vec![span],
            }
        }));
    }
}
