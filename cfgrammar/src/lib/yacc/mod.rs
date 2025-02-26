#![deny(unreachable_pub)]

pub mod ast;
pub mod firsts;
pub mod follows;
pub mod grammar;
pub mod parser;

pub use self::{
    grammar::{AssocKind, Precedence, SentenceGenerator, YaccGrammar},
    parser::{YaccGrammarError, YaccGrammarErrorKind, YaccGrammarWarning, YaccGrammarWarningKind},
};

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

#[derive(Clone, Copy, Debug)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub enum YaccKindResolver {
    /// The user can specify `%grmtools` in their grammar but unless it is compatible with this `YaccKind`, it's an error
    Force(YaccKind),
    /// Use `YaccKind` if the user doesn't specify `%grmtools` in their grammar
    Default(YaccKind),
    /// The user must specify `%grmtools` in their grammars or we throw an error
    NoDefault,
}

/// The particular Yacc variant this grammar makes use of.
#[derive(Clone, Copy, Debug)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
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
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub enum YaccOriginalActionKind {
    /// Execute user-specified actions attached to each production; also requires a %actiontype
    /// declaration.
    UserAction,
    /// Automatically create a parse tree instead of user-specified actions.
    GenericParseTree,
    /// Do not do execute actions of any sort.
    NoAction,
}
