#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

/// A `Span` records what portion of the user's input something (e.g. a lexeme or production)
/// references (i.e. the `Span` doesn't hold a reference / copy of the actual input).
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct Span {
    start: usize,
    end: usize,
}

impl Span {
    /// Create a new span starting at byte `start` and ending at byte `end`.
    ///
    /// # Panics
    ///
    /// If `end` is less than `start`.
    pub fn new(start: usize, end: usize) -> Self {
        if end < start {
            panic!("Span starts ({}) after it ends ({})!", start, end);
        }
        Span { start, end }
    }

    /// Byte offset of the start of the span.
    pub fn start(&self) -> usize {
        self.start
    }

    /// Byte offset of the end of the span.
    pub fn end(&self) -> usize {
        self.end
    }

    /// Length in bytes of the span.
    pub fn len(&self) -> usize {
        self.end - self.start
    }

    /// Returns `true` if this `Span` covers 0 bytes, or `false` otherwise.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}
