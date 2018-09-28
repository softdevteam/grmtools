use std::{error::Error, fmt, hash::Hash, mem::size_of};

use num_traits::{self, PrimInt, Unsigned};

#[derive(Copy, Clone, Debug)]
pub struct LexError {
    pub idx: usize
}

impl Error for LexError {
    fn cause(&self) -> Option<&Error> {
        None
    }
}

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
    fn next(&mut self) -> Option<Result<Lexeme<StorageT>, LexError>>;
    /// Return the line and column number of a `Lexeme`, or `Err` if it is out of bounds, or no
    /// line number information was collected.
    fn line_and_col(&self, &Lexeme<StorageT>) -> Result<(usize, usize), ()>;

    /// Return all this lexer's remaining lexemes or a `LexError` if there was a problem when lexing.
    fn all_lexemes(&mut self) -> Result<Vec<Lexeme<StorageT>>, LexError> {
        let mut lxs = Vec::new();
        let mut n = self.next();
        while let Some(r) = n {
            lxs.push(r?);
            n = self.next();
        }
        Ok(lxs)
    }
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Lexeme<StorageT> {
    // The long-term aim is to pack this struct so that len can be longer than u32 while everything
    // still fitting into 2 64-bit words.
    start: usize,
    len: u32,
    tok_id: StorageT
}

impl<StorageT: Copy> Lexeme<StorageT> {
    pub fn new(tok_id: StorageT, start: usize, len: usize) -> Self {
        Lexeme {
            start,
            len: num_traits::cast(len).unwrap(),
            tok_id
        }
    }

    /// The token ID.
    pub fn tok_id(&self) -> StorageT {
        self.tok_id
    }

    /// Byte offset of the start of the lexeme
    pub fn start(&self) -> usize {
        self.start
    }

    /// Byte offset of the start of the lexeme
    pub fn end(&self) -> usize {
        self.start() + self.len()
    }

    /// Length in bytes of the lexeme
    pub fn len(&self) -> usize {
        debug_assert!(size_of::<usize>() >= size_of::<u32>());
        self.len as usize
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }
}
