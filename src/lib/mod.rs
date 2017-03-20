#![feature(try_from)]

extern crate lrlex;
extern crate lrtable;

mod parser;
pub use parser::parse;
