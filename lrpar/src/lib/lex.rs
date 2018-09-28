use std::{error::Error, fmt, hash::Hash, mem::size_of};

use num_traits::{self, PrimInt, Unsigned};

#[derive(Debug)]
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

pub trait Lexer<StorageT: Hash + PrimInt + Unsigned> {
    fn lexemes(&mut self) -> Result<Vec<Lexeme<StorageT>>, LexError>;
    fn line_and_col(&self, &Lexeme<StorageT>) -> Result<(usize, usize), ()>;
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
