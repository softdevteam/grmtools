#![allow(clippy::len_without_is_empty)]

use std::{error::Error, fmt, hash::Hash, mem::size_of};

use num_traits::{PrimInt, Unsigned};
use static_assertions::const_assert;

use crate::Span;

/// A Lexing error.
#[derive(Copy, Clone, Debug)]
pub struct LexError {
    span: Span
}

impl LexError {
    pub fn new(span: Span) -> Self {
        LexError { span }
    }

    pub fn span(&self) -> Span {
        self.span
    }
}

impl Error for LexError {}

impl fmt::Display for LexError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "Couldn't lex input starting at byte {}",
            self.span.start()
        )
    }
}

/// The trait which all lexers which want to interact with `lrpar` must implement.
pub trait Lexer<'input, StorageT: Hash + PrimInt + Unsigned> {
    /// Iterate over all the lexemes in this lexer. Note that:
    ///   * The lexer may or may not stop after the first [LexError] is encountered.
    ///   * There are no guarantees about whether the lexer caches anything if this method is
    ///     called more than once (i.e. it might be slow to call this more than once).
    fn iter<'a>(&'a self) -> Box<dyn Iterator<Item = Result<Lexeme<StorageT>, LexError>> + 'a>;

    /// Return the user input associated with a [Span].
    ///
    /// # Panics
    ///
    /// If the span exceeds the known input.
    fn span_str(&self, span: Span) -> &'input str;

    /// Return the lines containing the input at `span` (including *all* the text on the lines
    /// that `span` starts and ends on).
    ///
    /// # Panics
    ///
    /// If the span exceeds the known input.
    fn span_lines_str(&self, span: Span) -> &'input str;

    /// Return `((start line, start column), (end line, end column))` for `span`. Note that column
    /// *characters* (not bytes) are returned.
    ///
    /// # Panics
    ///
    /// If the span exceeds the known input.
    fn line_col(&self, span: Span) -> ((usize, usize), (usize, usize));
}

/// A `Lexeme` represents a segment of the user's input that conforms to a known type. Note that
/// even if the type of a lexeme seemingly requires it to have `len() > 0` (e.g. integers might
/// match the regular expressions `[0-9]+`), error recovery might cause a lexeme to have a length
/// of 0. Users can detect the difference between a lexeme with an intentionally zero length from a
/// lexeme with zero length due to error recovery through the
/// [`inserted`](Lexeme::inserted) method.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Lexeme<StorageT> {
    // The long-term aim is to pack this struct so that len can be longer than u32 while everything
    // still fitting into 2 64-bit words.
    start: usize,
    len: u32,
    tok_id: StorageT
}

impl<StorageT: Copy> Lexeme<StorageT> {
    /// Create a new token with ID `tok_id` and a starting position in the input `start`. If the
    /// token is the result of user input, then `Some(n)` should be passed to `len`; if the token
    /// is the result of error recovery, then `None` should be passed to `len`.
    pub fn new(tok_id: StorageT, start: usize, len: Option<usize>) -> Self {
        const_assert!(size_of::<usize>() >= size_of::<u32>());
        let len = if let Some(l) = len {
            if l >= u32::max_value() as usize {
                panic!("Can't currently represent lexeme of length {}.", l);
            }
            l as u32
        } else {
            u32::max_value()
        };
        Lexeme { start, len, tok_id }
    }

    /// The token ID.
    pub fn tok_id(&self) -> StorageT {
        self.tok_id
    }

    /// Byte offset of the start of the lexeme
    #[deprecated(since = "0.6.1", note = "Please use span().start() instead")]
    pub fn start(&self) -> usize {
        self.start
    }

    /// Byte offset of the end of the lexeme.
    ///
    /// Note that if this lexeme was inserted by error recovery, it will end at the same place it
    /// started (i.e. `self.start() == self.end()`).
    #[deprecated(since = "0.6.1", note = "Please use span().end() instead")]
    pub fn end(&self) -> usize {
        self.span().end()
    }

    /// Length in bytes of the lexeme.
    ///
    /// Note that if this lexeme was inserted by error recovery, it will have a length of 0.
    #[deprecated(since = "0.6.1", note = "Please use span().len() instead")]
    pub fn len(&self) -> usize {
        self.span().len()
    }

    /// Obtain this `Lexeme`'s [Span].
    pub fn span(&self) -> Span {
        let end = if self.len == u32::max_value() {
            self.start
        } else {
            self.start + (self.len as usize)
        };
        Span::new(self.start, end)
    }

    /// Returns `true` if this lexeme was inserted as the result of error recovery, or `false`
    /// otherwise.
    pub fn inserted(&self) -> bool {
        self.len == u32::max_value()
    }
}

impl<StorageT: Copy> fmt::Display for Lexeme<StorageT> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Lexeme[{}..{}]", self.span().start(), self.span().end())
    }
}

impl<StorageT: Copy + fmt::Debug> Error for Lexeme<StorageT> {}
