#![allow(clippy::len_without_is_empty)]

use std::{error::Error, fmt, hash::Hash};

use crate::{Lexeme, Span};

type StorageT = u16;

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) struct TestLexeme {
    start: usize,
    len: usize,
    faulty: bool,
    tok_id: u16,
}

impl Lexeme<StorageT> for TestLexeme {
    fn new(tok_id: StorageT, start: usize, len: usize) -> Self {
        TestLexeme {
            start,
            len,
            faulty: false,
            tok_id,
        }
    }

    fn new_faulty(tok_id: StorageT, start: usize, len: usize) -> Self {
        TestLexeme {
            start,
            len,
            faulty: true,
            tok_id,
        }
    }

    fn tok_id(&self) -> StorageT {
        self.tok_id
    }

    fn span(&self) -> Span {
        Span::new(self.start, self.start + self.len)
    }

    fn faulty(&self) -> bool {
        self.faulty
    }
}

impl fmt::Display for TestLexeme {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "TestLexeme[{}..{}]",
            self.span().start(),
            self.span().end()
        )
    }
}

impl Error for TestLexeme {}
