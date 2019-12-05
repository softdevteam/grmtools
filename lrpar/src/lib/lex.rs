#![allow(clippy::len_without_is_empty)]

use std::{error::Error, fmt, hash::Hash, mem::size_of};

use num_traits::{PrimInt, Unsigned};
use static_assertions::const_assert;

/// A Lexing error.
#[derive(Copy, Clone, Debug)]
pub struct LexError {
    pub idx: usize
}

impl Error for LexError {}

impl fmt::Display for LexError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Couldn't lex input at position {}", self.idx)
    }
}

/// Roughly speaking, `Lexer` is an iterator which collectively produces `Lexeme`s, as well as
/// collecting the newlines encountered so that it can later optionally answer queries of the form
/// "what's the line and column number of lexeme L".
pub trait Lexer<StorageT: Hash + PrimInt + Unsigned> {
    /// Return the next `Lexeme` in the input or a `LexError`. Returns `None` if the input has been
    /// fully lexed (or if an error occurred which prevents further lexing).
    fn next(&self) -> Option<Result<Lexeme<StorageT>, LexError>>;

    /// Return the user input associated with a lexeme. Panics if the lexeme is invalid (i.e. was
    /// not produced by next()).
    fn lexeme_str(&self, lexeme: &Lexeme<StorageT>) -> &str;

    /// Return the line and column number of the byte at position `off`. Note that the column
    /// number is a character -- not a byte! -- offset, relative to the beginning of the line.
    /// Panics if the offset exceeds the known input.
    fn line_col(&self, off: usize) -> (usize, usize);

    /// Return the line containing the byte at position `off`. Panics if the offset exceeds the
    /// known input.
    fn surrounding_line_str(&self, off: usize) -> &str;

    /// Return all this lexer's remaining lexemes or a `LexError` if there was a problem when lexing.
    fn all_lexemes(&self) -> Result<Vec<Lexeme<StorageT>>, LexError> {
        let mut lxs = Vec::new();
        let mut n = self.next();
        while let Some(r) = n {
            lxs.push(r?);
            n = self.next();
        }
        Ok(lxs)
    }
}

/// A `Lexeme` represents a segment of the user's input that conforms to a known type. All lexemes
/// have a starting position in the user's input: lexemes that result from error recovery, however,
/// do not have a length (or, therefore, an end). This allows us to differentiate between lexemes
/// that are always of zero length (which are required in some grammars) from lexemes that result
/// from error recovery (where an error recovery algorithm can know the type that a lexeme should
/// have been, but can't know what its contents should have been).
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
    pub fn start(&self) -> usize {
        self.start
    }

    /// Byte offset of the end of the lexeme.
    ///
    /// Note that if this lexeme was inserted by error recovery, it will end at the same place it
    /// started (i.e. `self.start() == self.end()).
    pub fn end(&self) -> usize {
        if self.len == u32::max_value() {
            self.start
        } else {
            self.start + (self.len as usize)
        }
    }

    /// Length in bytes of the lexeme. Note that if this lexeme was inserted by error recovery, it
    /// will have a length of 0.
    pub fn len(&self) -> usize {
        if self.len == u32::max_value() {
            0
        } else {
            const_assert!(size_of::<usize>() >= size_of::<u32>());
            self.len as usize
        }
    }

    /// Returns `true` if this lexeme was inserted as the result of error recovery, or `false`
    /// otherwise.
    pub fn inserted(&self) -> bool {
        self.len == u32::max_value()
    }
}
