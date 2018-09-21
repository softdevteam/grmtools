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

#![feature(test)]

extern crate bincode;
extern crate cactus;
extern crate cfgrammar;
extern crate filetime;
#[macro_use]
extern crate indexmap;
extern crate lrlex;
extern crate lrtable;
extern crate num_traits;
extern crate rmp_serde as rmps;
extern crate serde;
extern crate test;
extern crate typename;
extern crate vob;

mod astar;
mod builder;
mod cpctplus;
mod panic;
pub mod parser;
pub use parser::{parse_rcvry, Node, ParseError, ParseRepair, RecoveryKind};
mod mf;

pub use builder::{reconstitute, ParserBuilder};

/// A convenience macro for including statically compiled `.y` files. A file `src/x.y` which is
/// statically compiled by lrpar can then be used in a crate with `lrpar_mod!(x)`.
#[macro_export]
macro_rules! lrpar_mod {
    ($n:ident) => {
        include!(concat!(env!("OUT_DIR"), "/", stringify!($n), ".rs"));
    };
}

#[doc(hidden)]
pub use cfgrammar::RIdx;
