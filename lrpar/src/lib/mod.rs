// Copyright (c) 2017 King's College London
// created by the Software Development Team <http://soft-dev.org/>
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0>, or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, or the UPL-1.0 license <http://opensource.org/licenses/UPL>
// at your option. This file may not be copied, modified, or distributed except according to those
// terms.

extern crate bincode;
extern crate cactus;
extern crate cfgrammar;
extern crate filetime;
#[macro_use]
extern crate indexmap;
#[macro_use]
extern crate lazy_static;
extern crate lrtable;
extern crate num_traits;
extern crate packedvec;
extern crate regex;
extern crate rmp_serde as rmps;
extern crate serde;
extern crate typename;
extern crate vob;

mod astar;
mod cpctplus;
pub mod ctbuilder;
pub mod lex;
pub use crate::lex::{LexError, Lexeme, Lexer};
mod panic;
pub mod parser;
pub use crate::parser::{
    LexParseError, Node, ParseError, ParseRepair, RTParserBuilder, RecoveryKind
};
mod mf;

pub use crate::ctbuilder::CTParserBuilder;

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
