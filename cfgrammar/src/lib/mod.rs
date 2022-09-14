#![allow(clippy::cognitive_complexity)]
#![allow(clippy::many_single_char_names)]
#![allow(clippy::new_without_default)]
#![allow(clippy::unnecessary_wraps)]
#![allow(clippy::upper_case_acronyms)]

//! A library for manipulating Context Free Grammars (CFG). It is impractical to fully homogenise
//! all the types of grammars out there, so the aim is for different grammar types
//! to have completely separate implementations. Code that wants to be generic over more than one
//! grammar type can then use an "adapter" to homogenise the particular grammar types of interest.
//! Currently this is a little academic, since only Yacc-style grammars are supported (albeit
//! several variants of Yacc grammars).
//!
//! Unfortunately, CFG terminology is something of a mess. Some people use different terms for the
//! same concept interchangeably; some use different terms to convey subtle differences of meaning
//! (but without complete uniformity). "Token", "terminal", and "lexeme" are examples of this: they
//! are synonyms in some tools and papers, but not in others.
//!
//! In order to make this library somewhat coherent, we therefore use some basic terminology
//! guidelines for major concepts (acknowledging that this will cause clashes with some grammar
//! types).
//!
//!   * A *grammar* is an ordered sequence of *productions*.
//!   * A *production* is an ordered sequence of *symbols*.
//!   * A *rule* maps a name to one or more productions.
//!   * A *token* is the name of a syntactic element.
//!
//! For example, in the following Yacc grammar:
//!
//!   R1: "a" "b" | R2;
//!   R2: "c";
//!
//! the following statements are true:
//!
//!   * There are 3 productions. 1: ["a", "b"] 2: ["R2"] 3: ["c"]`
//!   * There are two rules: R1 and R2. The mapping to productions is {R1: {1, 2}, R2: {3}}
//!   * There are three tokens: a, b, and c.
//!
//! cfgrammar makes the following guarantees about grammars:
//!
//!   * Productions are numbered from `0` to `prods_len() - 1` (inclusive).
//!   * Rules are numbered from `0` to `rules_len() - 1` (inclusive).
//!   * Tokens are numbered from `0` to `toks_len() - 1` (inclusive).
//!   * The StorageT type used to store productions, rules, and token indices can be infallibly
//!     converted into usize (see [`TIdx`](struct.TIdx.html) and friends for more details).
//!
//! For most current uses, the main function to investigate is
//! [`YaccGrammar::new()`](yacc/grammar/struct.YaccGrammar.html#method.new) and/or
//! [`YaccGrammar::new_with_storaget()`](yacc/grammar/struct.YaccGrammar.html#method.new_with_storaget)
//! which take as input a Yacc grammar.

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

pub mod analysis;
mod idxnewtype;
pub mod newlinecache;
pub mod span;
pub mod yacc;

pub use newlinecache::NewlineCache;
pub use span::{Span, Spanned};

/// A type specifically for rule indices.
pub use crate::idxnewtype::{PIdx, RIdx, SIdx, TIdx};

#[derive(Clone, Copy, Debug, Hash, Eq, PartialEq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub enum Symbol<StorageT> {
    Rule(RIdx<StorageT>),
    Token(TIdx<StorageT>),
}
