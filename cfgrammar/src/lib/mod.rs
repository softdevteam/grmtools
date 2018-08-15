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

//! A library for manipulating Context Free Grammars (CFG). At the moment it only really supports
//! Yacc-style grammars (albeit several variants of Yacc grammars), but the long-term aim is to
//! provide an API that, when possible, is agnostic about the type of grammar being manipulated.
//!
//! A note on the terminology we use, since there's no universal standard (and EBNF, which is
//! perhaps the closest we've got, uses terminology that now seems partially anachronistic):
//!
//!   * A rule is a mapping from a nonterminal name to 1 or more productions (the latter of which
//!     is often called 'alternatives').
//!   * A symbol is either a nonterminal or a terminal.
//!   * A production is a (possibly empty) ordered sequence of symbols.
//!
//! Every nonterminal has a corresponding rule (and thus the two concepts are interchangeable);
//! however, terminals are not required to appear in any production (such terminals can be used to
//! catch error conditions).
//!
//! We make the following guarantees about grammars:
//!
//!   * The grammar has a single start rule accessed by `start_rule_idx`.
//!   * The non-terminals are numbered from `0` to `nonterms_len() - 1` (inclusive).
//!   * The productions are numbered from `0` to `prods_len() - 1` (inclusive).
//!   * The terminals are numbered from `0` to `terms_len() - 1` (inclusive).
//!
//! This means that it is safe to write code such as:
//!
//! ```text
//! for i in 0..grm.nonterms_len() as usize {
//!   println!("{}", grm.nonterm_name(NTIdx::from(i)));
//! }
//! ```
//!
//! For most current uses, the main function to investigate is [`yacc_grm`](yacc/fn.yacc_grm.html)
//! which takes as input a Yacc grammar.

#![feature(try_from)]

use std::ops::Range;

#[macro_use] extern crate lazy_static;
extern crate indexmap;
extern crate num_traits;
#[cfg(feature="serde")]
#[macro_use]
extern crate serde;

use num_traits::{PrimInt, Unsigned};

mod idxnewtype;
pub mod yacc;

/// A type specifically for nonterminal indices.
pub use idxnewtype::{NTIdx, PIdx, SIdx, TIdx};

#[derive(Clone, Copy, Debug, Hash, Eq, PartialEq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub enum Symbol<StorageT> {
    Nonterm(NTIdx<StorageT>),
    Term(TIdx<StorageT>)
}

pub trait Grammar<StorageT: PrimInt + Unsigned> {
    /// How many terminals does this grammar have?
    fn terms_len(&self) -> u32;
    /// How many productions does this grammar have?
    fn prods_len(&self) -> PIdx<StorageT>;
    /// How many nonterminals does this grammar have?
    fn nonterms_len(&self) -> NTIdx<StorageT>;
    /// What is the index of the start rule?
    fn start_rule_idx(&self) -> NTIdx<StorageT>;

    /// Return an iterator which produces (in order from `0..self.nonterms_len()`) all this
    /// grammar's valid `NTIdx`s.
    fn iter_ntidxs(&self) -> Box<dyn Iterator<Item=NTIdx<StorageT>>> {
        Box::new((0..usize::from(self.nonterms_len())).map(|x| NTIdx(num_traits::cast(x).unwrap())))
    }

    fn iter_tidxs(&self, r: Range<u32>) -> Box<dyn Iterator<Item=TIdx<StorageT>>> {
        Box::new(r.map(|x| TIdx(num_traits::cast(x).unwrap())))
    }
}
