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
use proc_macro2::TokenStream;
use quote::quote;

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

/// The particular Yacc variant this grammar makes use of.
#[derive(Clone, Copy, Debug)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[non_exhaustive]
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

impl quote::ToTokens for YaccKind {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        tokens.extend(match *self {
            YaccKind::Grmtools => quote!(::cfgrammar::yacc::YaccKind::Grmtools),
            YaccKind::Original(action_kind) => {
                quote!(::cfgrammar::yacc::YaccKind::Original(#action_kind))
            }
            YaccKind::Eco => quote!(::cfgrammar::yacc::YaccKind::Eco),
        })
    }
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

impl quote::ToTokens for YaccOriginalActionKind {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        tokens.extend(match *self {
            YaccOriginalActionKind::UserAction => {
                quote!(::cfgrammar::yacc::YaccOriginalActionKind::UserAction)
            }
            YaccOriginalActionKind::GenericParseTree => {
                quote!(::cfgrammar::yacc::YaccOriginalActionKind::GenericParseTree)
            }
            YaccOriginalActionKind::NoAction => {
                quote!(::cfgrammar::yacc::YaccOriginalActionKind::NoAction)
            }
        })
    }
}
