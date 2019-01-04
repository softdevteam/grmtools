// Copyright (c) 2017 King's College London
// created by the Software Development Team <http://soft-dev.org/>
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0>, or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, or the UPL-1.0 license <http://opensource.org/licenses/UPL>
// at your option. This file may not be copied, modified, or distributed except according to those
// terms.

pub mod ast;
pub mod firsts;
pub mod follows;
pub mod grammar;
pub mod parser;

pub use self::{
    ast::{GrammarValidationError, GrammarValidationErrorKind},
    grammar::{AssocKind, Precedence, SentenceGenerator, YaccGrammar, YaccGrammarError},
    parser::{YaccParserError, YaccParserErrorKind}
};

/// The particular Yacc variant this grammar makes use of.
#[derive(Clone, Copy)]
pub enum YaccKind {
    /// The original Yacc style as documented by
    /// [Johnson](http://dinosaur.compilertools.net/yacc/index.html),
    Original(YaccOriginalActionKind),
    /// The variant used in the [Eco language composition editor](http://soft-dev.org/src/eco/)
    Eco
}

#[derive(Clone, Copy)]
pub enum YaccOriginalActionKind {
    /// Execute user-specified actions attached to each production; also requires a %actiontype
    /// declaration.
    UserAction,
    /// Automatically create a parse tree instead of user-specified actions.
    GenericParseTree,
    /// Do not do execute actions of any sort.
    NoAction
}
