#[cfg(feature = "bincode")]
use bincode::{Decode, Encode};
use proc_macro2::TokenStream;
use quote::{quote, ToTokens, TokenStreamExt};
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

/// A `Span` records what portion of the user's input something (e.g. a lexeme or production)
/// references (i.e. the `Span` doesn't hold a reference / copy of the actual input).
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[cfg_attr(feature = "bincode", derive(Encode, Decode))]
pub struct Span {
    start: usize,
    end: usize,
}

impl Span {
    /// Create a new span starting at byte `start` and ending at byte `end`.
    ///
    /// # Panics
    ///
    /// If `end` is less than `start`.
    pub fn new(start: usize, end: usize) -> Self {
        if end < start {
            panic!("Span starts ({}) after it ends ({})!", start, end);
        }
        Span { start, end }
    }

    /// Byte offset of the start of the span.
    pub fn start(&self) -> usize {
        self.start
    }

    /// Byte offset of the end of the span.
    pub fn end(&self) -> usize {
        self.end
    }

    /// Length in bytes of the span.
    pub fn len(&self) -> usize {
        self.end - self.start
    }

    /// Returns `true` if this `Span` covers 0 bytes, or `false` otherwise.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

/// Implemented for errors and warnings to provide access to their spans.
pub trait Spanned: std::fmt::Display {
    /// Returns the spans associated with the error, always containing at least 1 span.
    ///
    /// Refer to [SpansKind](crate::yacc::parser::SpansKind) via [spanskind](Self::spanskind)
    /// for the meaning and interpretation of spans and their ordering.
    fn spans(&self) -> &[Span];
    /// Returns the `SpansKind` associated with this error.
    fn spanskind(&self) -> crate::yacc::parser::SpansKind;
}

impl ToTokens for Span {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let Span { start, end } = self;
        tokens.append_all(quote! {::cfgrammar::Span::new(#start, #end)});
    }
}

/// A possibly inexact location which could either be a `Span`,
/// a command-line option, or some other location described textually.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Location {
    Span(Span),
    CommandLine,
    Other(String),
}

impl From<Span> for Location {
    fn from(span: Span) -> Location {
        Location::Span(span)
    }
}
