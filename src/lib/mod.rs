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

#[macro_use] extern crate lazy_static;
extern crate linked_hash_map;

mod u32struct;
pub mod yacc;

// A note on the terminology we use, since there's no universal standard (and EBNF, which is
// perhaps the closest we've got, uses terminology that now seems partially anachronistic):
//   A rule is a mapping from a nonterminal name to 1 or more productions (the latter of which is
//     often called 'alternatives').
//   A symbol is either a nonterminal or a terminal.
//   A production is a (possibly empty) ordered sequence of symbols.
//
// Every nonterminal has a corresponding rule; however, terminals are not required to appear in any
// production (such terminals can be used to catch error conditions).
//
// Internally, we assume that a grammar's start rule has a single production. Since we manually
// create the start rule ourselves (without relying on user input), this is a safe assumption.

pub use u32struct::{NTIdx, PIdx, SIdx, TIdx};

#[derive(Clone, Copy, Debug, Hash, Eq, PartialEq)]
pub enum Symbol {
    Nonterm(NTIdx),
    Term(TIdx)
}

pub trait Grammar {
    /// How many terminals does this grammar have?
    fn terms_len(&self) -> usize;
    /// How many productions does this grammar have?
    fn prods_len(&self) -> usize;
    /// How many nonterminals does this grammar have?
    fn nonterms_len(&self) -> usize;
    /// What is the index of the start rule?
    fn start_rule_idx(&self) -> NTIdx;
}
