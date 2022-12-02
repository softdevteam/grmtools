#![allow(clippy::len_without_is_empty)]

use std::{cmp, error::Error, fmt, hash::Hash, marker};

use cfgrammar::Span;
use num_traits::{PrimInt, Unsigned};

/// The base trait which all lexers which want to interact with `lrpar` must implement.
pub trait Lexer<LexemeT: Lexeme<StorageT>, StorageT: Hash + PrimInt + Unsigned, LexErrorT: LexError>
{
    /// Iterate over all the lexemes in this lexer. Note that:
    ///   * The lexer may or may not stop after the first [LexError] is encountered.
    ///   * There are no guarantees about what happens if this function is called more than once.
    ///     For example, a streaming lexer may only produce [Lexeme]s on the first call.
    fn iter<'a>(&'a self) -> Box<dyn Iterator<Item = Result<LexemeT, LexErrorT>> + 'a>;
}

/// A `NonStreamingLexer` is one that takes input in one go, and is then able to hand out
/// substrings to that input and calculate line and column numbers from a [Span].
pub trait NonStreamingLexer<
    'input,
    LexemeT: Lexeme<StorageT>,
    StorageT: Hash + PrimInt + Unsigned,
    LexErrorT: LexError,
>: Lexer<LexemeT, StorageT, LexErrorT>
{
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

/// A lexeme represents a segment of the user's input that conforms to a known type: this trait
/// captures the common behaviour of all lexeme structs.
///
/// Lexemes are assumed to have a definition which describes all possible correct lexemes (e.g. the
/// regular expression `[0-9]+` defines all integer lexemes). This trait also allows "faulty"
/// lexemes to be represented -- that is, lexemes that have resulted from error recovery of some
/// sort. Faulty lexemes can violate the lexeme's type definition in any possible way (e.g. they
/// might span more or less input than the definition would suggest is possible).
pub trait Lexeme<StorageT>: fmt::Debug + fmt::Display + cmp::Eq + Hash + marker::Copy {
    /// Create a new lexeme with ID `tok_id`, a starting position in the input `start`, and length
    /// `len`.
    ///
    /// Lexemes created using this function are expected to be "correct" in the sense that they
    /// fully respect the lexeme's definition semantics. To create faulty lexemes, use
    /// [new_faulty](Lexeme::new_faulty).
    fn new(tok_id: StorageT, start: usize, len: usize) -> Self
    where
        Self: Sized;

    /// Create a new faulty lexeme with ID `tok_id` and a starting position in the input `start`.
    fn new_faulty(tok_id: StorageT, start: usize, len: usize) -> Self
    where
        Self: Sized;

    /// The token ID.
    fn tok_id(&self) -> StorageT;

    /// Obtain this `Lexeme`'s [Span].
    fn span(&self) -> Span;

    /// Returns `true` if this lexeme is "faulty" i.e. is the result of error recovery in some way.
    /// If `true`, note that the lexeme's span may be greater or less than you may expect from the
    /// lexeme's definition.
    fn faulty(&self) -> bool;
}

/// A lexing error.
pub trait LexError: Error {
    /// Return the span associated with this error.
    fn span(&self) -> Span;
}
