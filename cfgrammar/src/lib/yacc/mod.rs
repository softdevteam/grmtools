pub mod ast;
pub mod firsts;
pub mod follows;
pub mod grammar;
pub mod parser;

pub use self::{
    ast::{GrammarValidationError, GrammarValidationErrorKind},
    grammar::{AssocKind, Precedence, SentenceGenerator, YaccGrammar, YaccGrammarError},
    parser::{YaccParserError, YaccParserErrorKind},
};

/// The particular Yacc variant this grammar makes use of.
#[derive(Clone, Copy, Debug)]
pub enum YaccKind {
    /// The original Yacc style as documented by
    /// [Johnson](http://dinosaur.compilertools.net/yacc/index.html),
    Original(YaccOriginalActionKind),
    /// Similar to the original Yacc style, but allowing individual rules' actions to have their
    /// own return type.
    Grmtools,
    /// The variant used in the [Eco language composition editor](http://soft-dev.org/src/eco/)
    Eco,
}

#[derive(Clone, Copy, Debug)]
pub enum YaccOriginalActionKind {
    /// Execute user-specified actions attached to each production; also requires a %actiontype
    /// declaration.
    UserAction,
    /// Automatically create a parse tree instead of user-specified actions.
    GenericParseTree,
    /// Do not do execute actions of any sort.
    NoAction,
}
