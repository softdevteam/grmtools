use std::{cmp, error::Error, fmt, hash::Hash, marker};

use cfgrammar::Span;
use lrpar::{Lexeme, LexerTypes};
use num_traits::{AsPrimitive, PrimInt, Unsigned};

use crate::LRLexError;

/// lrlex's standard [LexerTypes] `struct`, provided as a convenience.
#[derive(Debug, Clone)]
pub struct DefaultLexerTypes<T = u32>
where
    T: 'static + fmt::Debug + Hash + PrimInt + Unsigned,
    usize: AsPrimitive<T>,
{
    phantom: std::marker::PhantomData<T>,
}

impl<T> LexerTypes for DefaultLexerTypes<T>
where
    usize: AsPrimitive<T>,
    T: 'static + fmt::Debug + Hash + PrimInt + Unsigned,
{
    type LexemeT = DefaultLexeme<T>;
    type StorageT = T;
    type LexErrorT = LRLexError;
}

/// lrlex's standard lexeme struct, provided as a convenience.
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
