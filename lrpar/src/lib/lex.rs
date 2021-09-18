#![allow(clippy::len_without_is_empty)]

use std::{error::Error, fmt, hash::Hash, mem::size_of};

use num_traits::{PrimInt, Unsigned};
use static_assertions::const_assert;

use crate::Span;

/// A Lexing error.
#[derive(Copy, Clone, Debug)]
pub struct LexError {
    span: Span,
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

/// The base trait which all lexers which want to interact with `lrpar` must implement.
pub trait Lexer<StorageT: Hash + PrimInt + Unsigned> {
    /// Iterate over all the lexemes in this lexer. Note that:
    ///   * The lexer may or may not stop after the first [LexError] is encountered.
    ///   * There are no guarantees about what happens if this function is called more than once.
    ///     For example, a streaming lexer may only produce [Lexeme]s on the first call.
    fn iter<'a>(&'a self) -> Box<dyn Iterator<Item = Result<Lexeme<StorageT>, LexError>> + 'a>;
}

/// A `NonStreamingLexer` is one that takes input in one go, and is then able to hand out
/// substrings to that input and calculate line and column numbers from a [Span].
pub trait NonStreamingLexer<'input, StorageT: Hash + PrimInt + Unsigned>: Lexer<StorageT> {
    /// Return the user input associated with a [Span].
    ///
    /// The [Span] must be well formed:
    ///   * The start/end byte indexes must be valid UTF-8 character indexes.
    ///   * The end byte index must not exceed the input's length.
    ///
    /// If these requirements are not respected this function may panic or return unexpected
    /// portions of the input.
    fn span_str(&self, span: Span) -> &'input str;

    /// Return the lines containing the input at `span` (including *all* the text on the lines
    /// that `span` starts and ends on).
    ///
    /// The [Span] must be well formed:
    ///   * The start/end byte indexes must be valid UTF-8 character indexes.
    ///   * The end byte index must not exceed the input's length.
    ///
    /// If these requirements are not respected this function may panic or return unexpected
    /// portions of the input.
    fn span_lines_str(&self, span: Span) -> &'input str;

    /// Return `((start line, start column), (end line, end column))` for `span`. Note that column
    /// *characters* (not bytes) are returned.
    ///
    /// The [Span] must be well formed:
    ///   * The start/end byte indexes must be valid UTF-8 character indexes.
    ///   * The end byte index must not exceed the input's length.
    ///
    /// If these requirements are not respected this function may panic or return unexpected
    /// portions of the input.
    fn line_col(&self, span: Span) -> ((usize, usize), (usize, usize));
}

/// A `Lexeme` represents a segment of the user's input that conforms to a known type.
///
/// Lexemes are assumed to have a definition which describes all possible correct lexemes (e.g. the
/// regular expression `[0-9]+` defines all integer lexemes). This struct can also represent
/// "faulty" lexemes -- that is, lexemes that have resulted from error recovery of some sort.
/// Faulty lexemes can violate the lexeme's type definition in any possible way (e.g. they might
/// span more or less input than the definition would suggest is possible).
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Lexeme<StorageT> {
    // The long-term aim is to pack this struct so that len can be longer than u32 while everything
    // still fitting into 2 64-bit words.
    start: usize,
    len: u32,
    tok_id: StorageT,
}

impl<StorageT: Copy> Lexeme<StorageT> {
    /// Create a new lexeme with ID `tok_id`, a starting position in the input `start`, and length
    /// `len`.
    ///
    /// Lexemes created using this function are expected to be "correct" in the sense that they
    /// fully respect the lexeme's definition semantics. To create faulty lexemes, use
    /// [new_faulty](Lexeme::new_faulty).
    pub fn new(tok_id: StorageT, start: usize, len: usize) -> Self {
        const_assert!(size_of::<usize>() >= size_of::<u32>());
        if len >= u32::max_value() as usize {
            panic!("Can't currently represent lexeme of length {}.", len);
        }
        Lexeme {
            start,
            len: len as u32,
            tok_id,
        }
    }

    /// Create a new faulty lexeme with ID `tok_id` and a starting position in the input `start`.
    pub fn new_faulty(tok_id: StorageT, start: usize) -> Self {
        const_assert!(size_of::<usize>() >= size_of::<u32>());
        Lexeme {
            start,
            len: u32::max_value(),
            tok_id,
        }
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

    /// Returns `true` if this lexeme is "faulty" i.e. is the result of error recovery in some way.
    /// If `true`, note that the lexeme's span may be greater or less than you may expect from the
    /// lexeme's definition.
    pub fn faulty(&self) -> bool {
        self.len == u32::max_value()
    }
}

impl<StorageT: Copy> fmt::Display for Lexeme<StorageT> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Lexeme[{}..{}]", self.span().start(), self.span().end())
    }
}

impl<StorageT: Copy + fmt::Debug> Error for Lexeme<StorageT> {}
