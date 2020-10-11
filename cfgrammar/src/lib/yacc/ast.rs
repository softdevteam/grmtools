use std::{
    collections::{HashMap, HashSet},
    error::Error,
    fmt,
};

use indexmap::{IndexMap, IndexSet};

use super::Precedence;

/// An AST representing a grammar. This is built up gradually: when it is finished, the
/// `complete_and_validate` must be called exactly once in order to finish the set-up. At that
/// point, any further mutations made to the struct lead to undefined behaviour.
pub struct GrammarAST {
    pub start: Option<String>,
    // map from a rule name to indexes into prods
    pub rules: IndexMap<String, Rule>,
    pub prods: Vec<Production>,
    pub tokens: IndexSet<String>,
    pub precs: HashMap<String, Precedence>,
    pub avoid_insert: Option<HashSet<String>>,
    pub implicit_tokens: Option<HashSet<String>>,
    pub parse_param_bindings: Option<Vec<(String, String)>>,
    pub parse_param_lifetimes: Option<HashSet<String>>,
    // Error pretty-printers
    pub epp: HashMap<String, String>,
    pub programs: Option<String>,
}

#[derive(Debug)]
pub struct Rule {
    pub name: String,
    pub pidxs: Vec<usize>, // index into GrammarAST.prod
    pub actiont: Option<String>,
}

#[derive(Debug, Eq, PartialEq)]
pub struct Production {
    pub symbols: Vec<Symbol>,
    pub precedence: Option<String>,
    pub action: Option<String>,
}

#[derive(Clone, Debug, Hash, Eq, PartialEq)]
pub enum Symbol {
    Rule(String),
    Token(String),
}

/// The various different possible grammar validation errors.
#[derive(Debug)]
pub enum GrammarValidationErrorKind {
    NoStartRule,
    InvalidStartRule,
    UnknownRuleRef,
    UnknownToken,
    NoPrecForToken,
    UnknownEPP,
}

/// `GrammarAST` validation errors return an instance of this struct.
#[derive(Debug)]
pub struct GrammarValidationError {
    pub kind: GrammarValidationErrorKind,
    pub sym: Option<Symbol>,
}

impl Error for GrammarValidationError {}

impl fmt::Display for GrammarValidationError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.kind {
            GrammarValidationErrorKind::NoStartRule => write!(f, "No start rule specified"),
            GrammarValidationErrorKind::InvalidStartRule => write!(
                f,
                "Start rule '{}' does not appear in grammar",
                self.sym.as_ref().unwrap()
            ),
            GrammarValidationErrorKind::UnknownRuleRef => write!(
                f,
                "Unknown reference to rule '{}'",
                self.sym.as_ref().unwrap()
            ),
            GrammarValidationErrorKind::UnknownToken => {
                write!(f, "Unknown token '{}'", self.sym.as_ref().unwrap())
            }
            GrammarValidationErrorKind::NoPrecForToken => write!(
                f,
                "Token '{}' used in %prec has no precedence attached",
                self.sym.as_ref().unwrap()
            ),
            GrammarValidationErrorKind::UnknownEPP => write!(
                f,
                "Unknown token '{}' in %epp declaration",
                self.sym.as_ref().unwrap()
            ),
        }
    }
}

impl fmt::Display for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Symbol::Rule(ref s) => write!(f, "{}", s),
            Symbol::Token(ref s) => write!(f, "{}", s),
        }
    }
}

impl GrammarAST {
    pub fn new() -> GrammarAST {
        GrammarAST {
            start: None,
            rules: IndexMap::new(), // Using an IndexMap means that we retain the order
            // of rules as they're found in the input file.
            prods: Vec::new(),
            tokens: IndexSet::new(),
            precs: HashMap::new(),
            avoid_insert: None,
            implicit_tokens: None,
            epp: HashMap::new(),
            programs: None,
            parse_param_bindings: None,
            parse_param_lifetimes: None,
        }
    }

    pub fn add_rule(&mut self, name: String, actiont: Option<String>) {
        self.rules.insert(
            name.clone(),
            Rule {
                name,
                pidxs: Vec::new(),
                actiont,
            },
        );
    }

    pub fn add_prod(
        &mut self,
        rule_name: String,
        symbols: Vec<Symbol>,
        precedence: Option<String>,
        action: Option<String>,
    ) {
        self.rules[&rule_name].pidxs.push(self.prods.len());
        self.prods.push(Production {
            symbols,
            precedence,
            action,
        });
    }

    pub fn add_programs(&mut self, s: String) {
        self.programs = Some(s)
    }

    pub fn get_rule(&self, key: &str) -> Option<&Rule> {
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
    ///   5) Every token declared with %epp matches a known token
    /// If the validation succeeds, None is returned.
    pub(crate) fn complete_and_validate(&mut self) -> Result<(), GrammarValidationError> {
        match self.start {
            None => {
                return Err(GrammarValidationError {
                    kind: GrammarValidationErrorKind::NoStartRule,
                    sym: None,
                });
            }
            Some(ref s) => {
                if !self.rules.contains_key(s) {
                    return Err(GrammarValidationError {
                        kind: GrammarValidationErrorKind::InvalidStartRule,
                        sym: Some(Symbol::Rule(s.clone())),
                    });
                }
            }
        }
        for rule in self.rules.values() {
            for &pidx in &rule.pidxs {
                let prod = &self.prods[pidx];
                if let Some(ref n) = prod.precedence {
                    if !self.tokens.contains(n) {
                        return Err(GrammarValidationError {
                            kind: GrammarValidationErrorKind::UnknownToken,
                            sym: Some(Symbol::Token(n.clone())),
                        });
                    }
                    if !self.precs.contains_key(n) {
                        return Err(GrammarValidationError {
                            kind: GrammarValidationErrorKind::NoPrecForToken,
                            sym: Some(Symbol::Token(n.clone())),
                        });
                    }
                }
                for sym in &prod.symbols {
                    match *sym {
                        Symbol::Rule(ref name) => {
                            if !self.rules.contains_key(name) {
                                return Err(GrammarValidationError {
                                    kind: GrammarValidationErrorKind::UnknownRuleRef,
                                    sym: Some(sym.clone()),
                                });
                            }
                        }
                        Symbol::Token(ref name) => {
                            if !self.tokens.contains(name) {
                                return Err(GrammarValidationError {
                                    kind: GrammarValidationErrorKind::UnknownToken,
                                    sym: Some(sym.clone()),
                                });
                            }
                        }
                    }
                }
            }
        }
        for k in self.epp.keys() {
            if self.tokens.contains(k) {
                continue;
            }
            if let Some(ref it) = self.implicit_tokens {
                if it.contains(k) {
                    continue;
                }
            }
            return Err(GrammarValidationError {
                kind: GrammarValidationErrorKind::UnknownEPP,
                sym: Some(Symbol::Token(k.clone())),
            });
        }
        Ok(())
    }
}

#[cfg(test)]
mod test {
    use super::{
        super::{AssocKind, Precedence},
        GrammarAST, GrammarValidationError, GrammarValidationErrorKind, Symbol,
    };

    fn rule(n: &str) -> Symbol {
        Symbol::Rule(n.to_string())
    }

    fn token(n: &str) -> Symbol {
        Symbol::Token(n.to_string())
    }

    #[test]
    fn test_empty_grammar() {
        let mut grm = GrammarAST::new();
        match grm.complete_and_validate() {
            Err(GrammarValidationError {
                kind: GrammarValidationErrorKind::NoStartRule,
                ..
            }) => (),
            _ => panic!("Validation error"),
        }
    }

    #[test]
    fn test_invalid_start_rule() {
        let mut grm = GrammarAST::new();
        grm.start = Some("A".to_string());
        grm.add_rule("B".to_string(), None);
        grm.add_prod("B".to_string(), vec![], None, None);
        match grm.complete_and_validate() {
            Err(GrammarValidationError {
                kind: GrammarValidationErrorKind::InvalidStartRule,
                ..
            }) => (),
            _ => panic!("Validation error"),
        }
    }

    #[test]
    fn test_valid_start_rule() {
        let mut grm = GrammarAST::new();
        grm.start = Some("A".to_string());
        grm.add_rule("A".to_string(), None);
        grm.add_prod("A".to_string(), vec![], None, None);
        assert!(grm.complete_and_validate().is_ok());
    }

    #[test]
    fn test_valid_rule_ref() {
        let mut grm = GrammarAST::new();
        grm.start = Some("A".to_string());
        grm.add_rule("A".to_string(), None);
        grm.add_rule("B".to_string(), None);
        grm.add_prod("A".to_string(), vec![rule("B")], None, None);
        grm.add_prod("B".to_string(), vec![], None, None);
        assert!(grm.complete_and_validate().is_ok());
    }

    #[test]
    fn test_invalid_rule_ref() {
        let mut grm = GrammarAST::new();
        grm.start = Some("A".to_string());
        grm.add_rule("A".to_string(), None);
        grm.add_prod("A".to_string(), vec![rule("B")], None, None);
        match grm.complete_and_validate() {
            Err(GrammarValidationError {
                kind: GrammarValidationErrorKind::UnknownRuleRef,
                ..
            }) => (),
            _ => panic!("Validation error"),
        }
    }

    #[test]
    fn test_valid_token_ref() {
        let mut grm = GrammarAST::new();
        grm.tokens.insert("b".to_string());
        grm.start = Some("A".to_string());
        grm.add_rule("A".to_string(), None);
        grm.add_prod("A".to_string(), vec![token("b")], None, None);
        assert!(grm.complete_and_validate().is_ok());
    }

    #[test]
    fn test_redefine_rules_as_tokens() {
        // for now we won't support the YACC feature that allows
        // to redefine rules as tokens by adding them to '%token'
        let mut grm = GrammarAST::new();
        grm.tokens.insert("b".to_string());
        grm.start = Some("A".to_string());
        grm.add_rule("A".to_string(), None);
        grm.add_prod("A".to_string(), vec![rule("b")], None, None);
        assert!(grm.complete_and_validate().is_err());
    }

    #[test]
    fn test_invalid_token_ref() {
        let mut grm = GrammarAST::new();
        grm.start = Some("A".to_string());
        grm.add_rule("A".to_string(), None);
        grm.add_prod("A".to_string(), vec![token("b")], None, None);
        match grm.complete_and_validate() {
            Err(GrammarValidationError {
                kind: GrammarValidationErrorKind::UnknownToken,
                ..
            }) => (),
            _ => panic!("Validation error"),
        }
    }

    #[test]
    fn test_invalid_rule_forgotten_token() {
        let mut grm = GrammarAST::new();
        grm.start = Some("A".to_string());
        grm.add_rule("A".to_string(), None);
        grm.add_prod("A".to_string(), vec![rule("b"), token("b")], None, None);
        match grm.complete_and_validate() {
            Err(GrammarValidationError {
                kind: GrammarValidationErrorKind::UnknownRuleRef,
                ..
            }) => (),
            _ => panic!("Validation error"),
        }
    }

    #[test]
    fn test_invalid_epp() {
        let mut grm = GrammarAST::new();
        grm.start = Some("A".to_string());
        grm.add_rule("A".to_string(), None);
        grm.add_prod("A".to_string(), vec![], None, None);
        grm.epp.insert("k".to_owned(), "v".to_owned());
        match grm.complete_and_validate() {
            Err(GrammarValidationError {
                kind: GrammarValidationErrorKind::UnknownEPP,
                ..
            }) => (),
            _ => panic!("Validation error"),
        }
    }

    #[test]
    fn test_precedence_override() {
        let mut grm = GrammarAST::new();
        grm.precs.insert(
            "b".to_string(),
            Precedence {
                level: 1,
                kind: AssocKind::Left,
            },
        );
        grm.start = Some("A".to_string());
        grm.tokens.insert("b".to_string());
        grm.add_rule("A".to_string(), None);
        grm.add_prod(
            "A".to_string(),
            vec![token("b")],
            Some("b".to_string()),
            None,
        );
        assert!(grm.complete_and_validate().is_ok());
    }

    #[test]
    fn test_invalid_precedence_override() {
        let mut grm = GrammarAST::new();
        grm.start = Some("A".to_string());
        grm.add_rule("A".to_string(), None);
        grm.add_prod(
            "A".to_string(),
            vec![token("b")],
            Some("b".to_string()),
            None,
        );
        match grm.complete_and_validate() {
            Err(GrammarValidationError {
                kind: GrammarValidationErrorKind::UnknownToken,
                ..
            }) => (),
            _ => panic!("Validation error"),
        }
        grm.tokens.insert("b".to_string());
        match grm.complete_and_validate() {
            Err(GrammarValidationError {
                kind: GrammarValidationErrorKind::NoPrecForToken,
                ..
            }) => (),
            _ => panic!("Validation error"),
        }
    }
}
