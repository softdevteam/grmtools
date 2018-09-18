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

use std::collections::{HashMap, HashSet};
use std::error::Error;
use std::fmt;

use indexmap::{IndexMap, IndexSet};

use yacc::Precedence;

/// An AST representing a grammar. This is built up gradually: when it is finished, the
/// `complete_and_validate` must be called exactly once in order to finish the set-up. At that
/// point, any further mutations made to the struct lead to undefined behaviour.
pub struct GrammarAST {
    pub start: Option<String>,
    // map from a rule name to indexes into prods
    pub rules: IndexMap<String, Vec<usize>>,
    pub prods: Vec<Production>,
    pub tokens: IndexSet<String>,
    pub precs: HashMap<String, Precedence>,
    pub implicit_tokens: Option<HashSet<String>>
}

#[derive(Debug)]
pub struct Rule {
    pub name: String,
    pub pidxs: Vec<usize> // index into GrammarAST.prod
}

#[derive(Debug, Eq, PartialEq)]
pub struct Production {
    pub symbols: Vec<Symbol>,
    pub precedence: Option<String>
}

#[derive(Clone, Debug, Hash, Eq, PartialEq)]
pub enum Symbol {
    Rule(String),
    Token(String)
}

/// The various different possible grammar validation errors.
#[derive(Debug)]
pub enum GrammarValidationErrorKind {
    NoStartRule,
    InvalidStartRule,
    UnknownRuleRef,
    UnknownToken,
    NoPrecForToken
}

/// `GrammarAST` validation errors return an instance of this struct.
#[derive(Debug)]
pub struct GrammarValidationError {
    pub kind: GrammarValidationErrorKind,
    pub sym: Option<Symbol>
}

impl Error for GrammarValidationError {}

impl fmt::Display for GrammarValidationError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.kind {
            GrammarValidationErrorKind::NoStartRule => {
                write!(f, "No start rule specified")
            },
            GrammarValidationErrorKind::InvalidStartRule => {
                write!(f, "Start rule '{}' does not appear in grammar", self.sym.as_ref().unwrap())
            },
            GrammarValidationErrorKind::UnknownRuleRef => {
                write!(f, "Unknown reference to rule '{}'", self.sym.as_ref().unwrap())
            },
            GrammarValidationErrorKind::UnknownToken => {
                write!(f, "Unknown token '{}'", self.sym.as_ref().unwrap())
            },
            GrammarValidationErrorKind::NoPrecForToken => {
                write!(f, "Token '{}' used in %prec has no precedence attached", self.sym.as_ref().unwrap())
            }
        }
    }
}

impl fmt::Display for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Symbol::Rule(ref s) => write!(f, "{}", s),
            Symbol::Token(ref s)    => write!(f, "{}", s)
        }
    }
}

impl GrammarAST {
    pub fn new() -> GrammarAST {
        GrammarAST {
            start:  None,
            rules:  IndexMap::new(), // Using an IndexMap means that we retain the order
                                     // of rules as they're found in the input file.
            prods:  Vec::new(),
            tokens: IndexSet::new(),
            precs:  HashMap::new(),
            implicit_tokens: None
        }
    }

    pub fn add_prod(&mut self, key: String, symbols: Vec<Symbol>, precedence: Option<String>) {
        self.rules.entry(key)
                  .or_insert_with(Vec::new)
                  .push(self.prods.len());
        self.prods.push(Production{symbols, precedence});
    }

    pub fn get_rule(&self, key: &str) -> Option<&Vec<usize>>{
        self.rules.get(key)
    }

    pub fn has_token(&self, s: &str) -> bool {
        self.tokens.contains(s)
    }

    /// After the AST has been populated, perform any final operations, and validate the grammar
    /// checking that:
    ///   1) The start rule references a rule in the grammar
    ///   2) Every rule reference references a rule in the grammar
    ///   3) Every token reference references a declared token
    ///   4) If a production has a precedence token, then it references a declared token
    /// If the validation succeeds, None is returned.
    pub(crate) fn complete_and_validate(&mut self) -> Result<(), GrammarValidationError> {
        match self.start {
            None => {
                return Err(GrammarValidationError{kind: GrammarValidationErrorKind::NoStartRule,
                                                  sym: None})
            },
            Some(ref s) => {
                if !self.rules.contains_key(s) {
                    return Err(GrammarValidationError{kind: GrammarValidationErrorKind::InvalidStartRule,
                                               sym: Some(Symbol::Rule(s.clone()))});
                }
            }
        }
        for pidxs in self.rules.values() {
            for &pidx in pidxs {
                let prod = &self.prods[pidx];
                if let Some(ref n) = prod.precedence {
                    if !self.tokens.contains(n) {
                        return Err(GrammarValidationError{kind: GrammarValidationErrorKind::UnknownToken,
                            sym: Some(Symbol::Token(n.clone()))});
                    }
                    if !self.precs.contains_key(n) {
                        return Err(GrammarValidationError{kind: GrammarValidationErrorKind::NoPrecForToken,
                            sym: Some(Symbol::Token(n.clone()))});
                    }
                }
                for sym in &prod.symbols {
                    match *sym {
                        Symbol::Rule(ref name) => {
                            if !self.rules.contains_key(name) {
                                return Err(GrammarValidationError{kind: GrammarValidationErrorKind::UnknownRuleRef,
                                    sym: Some(sym.clone())});
                            }
                        }
                        Symbol::Token(ref name) => {
                            if !self.tokens.contains(name) {
                                return Err(GrammarValidationError{kind: GrammarValidationErrorKind::UnknownToken,
                                    sym: Some(sym.clone())});
                            }
                        }
                    }
                }
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod test {
    use super::{GrammarAST, GrammarValidationError, GrammarValidationErrorKind, Symbol};
    use yacc::{AssocKind, Precedence};

    fn rule(n: &str) -> Symbol {
        Symbol::Rule(n.to_string())
    }

    fn token(n: &str) -> Symbol {
        Symbol::Token(n.to_string())
    }

    #[test]
    fn test_empty_grammar(){
        let mut grm = GrammarAST::new();
        match grm.complete_and_validate() {
            Err(GrammarValidationError{kind: GrammarValidationErrorKind::NoStartRule, ..}) => (),
            _ => panic!("Validation error")
        }
    }

    #[test]
    fn test_invalid_start_rule(){
        let mut grm = GrammarAST::new();
        grm.start = Some("A".to_string());
        grm.add_prod("B".to_string(), vec!(), None);
        match grm.complete_and_validate() {
            Err(GrammarValidationError{kind: GrammarValidationErrorKind::InvalidStartRule, ..}) => (),
            _ => panic!("Validation error")
        }
    }

    #[test]
    fn test_valid_start_rule(){
        let mut grm = GrammarAST::new();
        grm.start = Some("A".to_string());
        grm.add_prod("A".to_string(), vec!(), None);
        assert!(grm.complete_and_validate().is_ok());
    }

    #[test]
    fn test_valid_rule_ref(){
        let mut grm = GrammarAST::new();
        grm.start = Some("A".to_string());
        grm.add_prod("A".to_string(), vec!(rule("B")), None);
        grm.add_prod("B".to_string(), vec!(), None);
        assert!(grm.complete_and_validate().is_ok());
    }

    #[test]
    fn test_invalid_rule_ref(){
        let mut grm = GrammarAST::new();
        grm.start = Some("A".to_string());
        grm.add_prod("A".to_string(), vec!(rule("B")), None);
        match grm.complete_and_validate() {
            Err(GrammarValidationError{kind: GrammarValidationErrorKind::UnknownRuleRef, ..}) => (),
            _ => panic!("Validation error")
        }
    }

    #[test]
    fn test_valid_token_ref(){
        let mut grm = GrammarAST::new();
        grm.tokens.insert("b".to_string());
        grm.start = Some("A".to_string());
        grm.add_prod("A".to_string(), vec!(token("b")), None);
        assert!(grm.complete_and_validate().is_ok());
    }

    #[test]
    fn test_redefine_rules_as_tokens(){
        // for now we won't support the YACC feature that allows
        // to redefine rules as tokens by adding them to '%token'
        let mut grm = GrammarAST::new();
        grm.tokens.insert("b".to_string());
        grm.start = Some("A".to_string());
        grm.add_prod("A".to_string(), vec!(rule("b")), None);
        assert!(grm.complete_and_validate().is_err());
    }

    #[test]
    fn test_invalid_token_ref(){
        let mut grm = GrammarAST::new();
        grm.start = Some("A".to_string());
        grm.add_prod("A".to_string(), vec!(token("b")), None);
        match grm.complete_and_validate() {
            Err(GrammarValidationError{kind: GrammarValidationErrorKind::UnknownToken, ..}) => (),
            _ => panic!("Validation error")
        }
    }

    #[test]
    fn test_invalid_rule_forgotten_token(){
        let mut grm = GrammarAST::new();
        grm.start = Some("A".to_string());
        grm.add_prod("A".to_string(), vec!(rule("b"), token("b")), None);
        match grm.complete_and_validate() {
            Err(GrammarValidationError{kind: GrammarValidationErrorKind::UnknownRuleRef, ..}) => (),
            _ => panic!("Validation error")
        }
    }

    #[test]
    fn test_precedence_override(){
        let mut grm = GrammarAST::new();
        grm.precs.insert("b".to_string(), Precedence{level: 1, kind: AssocKind::Left});
        grm.start = Some("A".to_string());
        grm.tokens.insert("b".to_string());
        grm.add_prod("A".to_string(), vec!(token("b")), Some("b".to_string()));
        assert!(grm.complete_and_validate().is_ok());
    }

    #[test]
    fn test_invalid_precedence_override(){
        let mut grm = GrammarAST::new();
        grm.start = Some("A".to_string());
        grm.add_prod("A".to_string(), vec!(token("b")), Some("b".to_string()));
        match grm.complete_and_validate() {
            Err(GrammarValidationError{kind: GrammarValidationErrorKind::UnknownToken, ..}) => (),
            _ => panic!("Validation error")
        }
        grm.tokens.insert("b".to_string());
        match grm.complete_and_validate() {
            Err(GrammarValidationError{kind: GrammarValidationErrorKind::NoPrecForToken, ..}) => (),
            _ => panic!("Validation error")
        }
    }
}
