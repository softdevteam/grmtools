#![allow(clippy::len_without_is_empty)]
#![allow(unused)]

use std::{error::Error, fmt, hash::Hash};

use cfgrammar::Span;

use crate::{LexError, Lexeme, LexerTypes};

type StorageT = u16;

#[derive(Debug)]
pub(crate) struct TestLexerTypes();

impl LexerTypes for TestLexerTypes {
    type LexemeT = TestLexeme;
    type StorageT = u16;
    type LexErrorT = TestLexError;
}

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

#[derive(Debug)]
pub(crate) struct TestLexError {}

impl LexError for TestLexError {
    fn span(&self) -> Span {
        unreachable!()
    }
}

impl Error for TestLexError {}

impl fmt::Display for TestLexError {
    fn fmt(&self, _: &mut fmt::Formatter) -> fmt::Result {
        unreachable!();
    }
}

#[macro_export]
#[cfg(test)]
macro_rules! header_for_yacckind {
    ($yk:expr) => {{
        use cfgrammar::header::{Header, Value};
        use cfgrammar::markmap::{Entry, MergeBehavior};
        use cfgrammar::Location;

        let mut header = Header::new();
        match header.entry("yacckind".to_string()) {
            Entry::Occupied(_) => unreachable!("Header should be empty"),
            Entry::Vacant(v) => {
                let mut o = v.insert_entry((
                    Location::Other("Testsuite".to_string()),
                    Value::try_from($yk).unwrap(),
                ));
                o.mark_required();
                o.set_merge_behavior(MergeBehavior::Ours);
            }
        };
        header
    }};
}

pub use header_for_yacckind;
