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

#![feature(try_from)]

extern crate cfgrammar;
extern crate fnv;
extern crate num_traits;
#[cfg(feature="serde")]
#[macro_use]
extern crate serde;
extern crate vob;

use std::hash::Hash;

use num_traits::{AsPrimitive, PrimInt, Unsigned};

mod firsts;
mod itemset;
mod pager;
mod stategraph;
pub mod statetable;

use cfgrammar::yacc::YaccGrammar;
pub use stategraph::StateGraph;
pub use statetable::{Action, StateTable, StateTableError, StateTableErrorKind};

type StIdxStorageT = u32;

/// StIdx is a wrapper for a 32-bit state index.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
// The biggest grammars I'm currently aware of have just over 1000 states, so in practise it
// looks like a u16 is always big enough to store state indexes. So, for as long as we can get
// away with it, we only store u16. Nevertheless, we tell the world we only deal in u32 so that
// we can change our storage to u32 later transparently.
pub struct StIdx(u16);

impl From<u32> for StIdx {
    fn from(v: u32) -> Self {
        if v > u32::from(u16::max_value()) {
            panic!("Overflow");
        }
        StIdx(v as u16)
    }
}

impl From<usize> for StIdx {
    fn from(v: usize) -> Self {
        if v > usize::from(u16::max_value()) {
            panic!("Overflow");
        }
        StIdx(v as u16)
    }
}

impl From<StIdx> for usize {
    fn from(st: StIdx) -> Self {
        st.0 as usize
    }
}

impl From<StIdx> for u32 {
    fn from(st: StIdx) -> Self {
        st.0 as u32
    }
}

#[derive(Clone, Copy)]
pub enum Minimiser {
    Pager
}

pub fn from_yacc<StorageT: 'static + Hash + PrimInt + Unsigned>
                (grm: &YaccGrammar<StorageT>, m: Minimiser)
              -> Result<(StateGraph<StorageT>, StateTable<StorageT>), StateTableError<StorageT>>
           where usize: AsPrimitive<StorageT>
{
    match m {
        Minimiser::Pager => {
            let sg = pager::pager_stategraph(grm);
            let st = try!(StateTable::new(grm, &sg));
            Ok((sg, st))
        }
    }
}
