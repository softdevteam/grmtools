// Copyright (c) 2017 King's College London
// created by the Software Development Team <http://soft-dev.org/>
//
// The Universal Permissive License (UPL), Version 1.0
//
// Subject to the condition set forth below, permission is hereby granted to any person obtaining a
// copy of this software, associated documentation and/or data (collectively the "Software"), free
// of charge and under any and all copyright rights in the Software, and any and all patent rights
// owned or freely licensable by each licensor hereunder covering either (i) the unmodified
// Software as contributed to or provided by such licensor, or (ii) the Larger Works (as defined
// below), to deal in both
//
// (a) the Software, and
// (b) any piece of software and/or hardware listed in the lrgrwrks.txt file
// if one is included with the Software (each a "Larger Work" to which the Software is contributed
// by such licensors),
//
// without restriction, including without limitation the rights to copy, create derivative works
// of, display, perform, and distribute the Software and make, use, sell, offer for sale, import,
// export, have made, and have sold the Software and the Larger Work(s), and to sublicense the
// foregoing rights on either these or other terms.
//
// This license is subject to the following condition: The above copyright notice and either this
// complete permission notice or at a minimum a reference to the UPL must be included in all copies
// or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING
// BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
// NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
// DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

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

#[macro_use] extern crate lazy_static;
extern crate indexmap;
extern crate num_traits;
#[cfg(feature="serde")] #[macro_use] extern crate serde;
extern crate vob;

use num_traits::{AsPrimitive, PrimInt, Unsigned};
use vob::Vob;

mod idxnewtype;
pub mod yacc;

/// A type specifically for nonterminal indices.
pub use idxnewtype::{RIdx, PIdx, SIdx, TIdx};

#[derive(Clone, Copy, Debug, Hash, Eq, PartialEq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub enum Symbol<StorageT> {
    Nonterm(RIdx<StorageT>),
    Term(TIdx<StorageT>)
}

pub trait Grammar<StorageT: 'static + PrimInt + Unsigned> where usize: AsPrimitive<StorageT> {
    /// How many productions does this grammar have?
    fn prods_len(&self) -> PIdx<StorageT>;
    /// How many nonterminals does this grammar have?
    fn rules_len(&self) -> RIdx<StorageT>;
    /// What is the index of the start rule?
    fn start_rule_idx(&self) -> RIdx<StorageT>;
    /// How many terminals does this grammar have?
    fn terms_len(&self) -> TIdx<StorageT>;

    /// Return an iterator which produces (in order from `0..self.rules_len()`) all this
    /// grammar's valid `RIdx`s.
    fn iter_rules(&self) -> Box<dyn Iterator<Item=RIdx<StorageT>>>
    {
        // We can use as_ safely, because we know that we're only generating integers from
        // 0..self.rules_len() and, since rules_len() returns an RIdx<StorageT>, then by
        // definition the integers we're creating fit within StorageT.
        Box::new((0..usize::from(self.rules_len())).map(|x| RIdx(x.as_())))
    }

    /// Return an iterator which produces (in order from `0..self.prods_len()`) all this
    /// grammar's valid `PIdx`s.
    fn iter_pidxs(&self) -> Box<dyn Iterator<Item=PIdx<StorageT>>>
    {
        // We can use as_ safely, because we know that we're only generating integers from
        // 0..self.rules_len() and, since rules_len() returns an RIdx<StorageT>, then by
        // definition the integers we're creating fit within StorageT.
        Box::new((0..usize::from(self.prods_len())).map(|x| PIdx(x.as_())))
    }

    fn iter_tidxs(&self) -> Box<dyn Iterator<Item=TIdx<StorageT>>>
    {
        // We can use as_ safely, because we know that we're only generating integers from
        // 0..self.rules_len() and, since rules_len() returns an TIdx<StorageT>, then by
        // definition the integers we're creating fit within StorageT.
        Box::new((0..usize::from(self.terms_len())).map(|x| TIdx(x.as_())))
    }

    fn firsts(&self) -> Box<dyn Firsts<StorageT>>;
}

pub trait Firsts<StorageT: 'static + PrimInt + Unsigned> where usize: AsPrimitive<StorageT> {
    /// Return all the firsts for nonterminal `ntidx`.
    fn firsts(&self, ntidx: RIdx<StorageT>) -> &Vob;

    /// Returns true if the terminal `tidx` is in the first set for nonterminal `nidx`.
    fn is_set(&self, nidx: RIdx<StorageT>, tidx: TIdx<StorageT>) -> bool;

    /// Returns true if the nonterminal `ntidx` has epsilon in its first set.
    fn is_epsilon_set(&self, ntidx: RIdx<StorageT>) -> bool;

    /// Ensures that the firsts bit for terminal `tidx` nonterminal `nidx` is set. Returns true if
    /// it was already set, or false otherwise.
    fn set(&mut self, ntidx: RIdx<StorageT>, tidx: TIdx<StorageT>) -> bool;
}
