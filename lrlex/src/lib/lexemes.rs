use std::{cmp, error::Error, fmt, hash::Hash, marker};

use cfgrammar::Span;
use lrpar::Lexeme;

/// lrlex's standard lexeme struct: all lexemes are instances of this struct.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct DefaultLexeme<StorageT: fmt::Debug = u32> {
    start: usize,
    len: usize,
    faulty: bool,
    tok_id: StorageT,
}

impl<StorageT: Copy + fmt::Debug + Hash + cmp::Eq> Lexeme<StorageT> for DefaultLexeme<StorageT> {
    fn new(tok_id: StorageT, start: usize, len: usize) -> Self {
        DefaultLexeme {
            start,
            len,
            faulty: false,
            tok_id,
        }
    }

    fn new_faulty(tok_id: StorageT, start: usize, len: usize) -> Self {
        DefaultLexeme {
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

impl<StorageT: Copy + fmt::Debug + cmp::Eq + Hash + marker::Copy> fmt::Display
    for DefaultLexeme<StorageT>
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "DefaultLexeme[{}..{}]",
            self.span().start(),
            self.span().end()
        )
    }
}

impl<StorageT: Copy + fmt::Debug + cmp::Eq + Hash + marker::Copy> Error
    for DefaultLexeme<StorageT>
{
}
