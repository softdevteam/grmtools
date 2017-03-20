use std::collections::{HashMap, HashSet};
use std::fmt;

use grammar::Precedence;

pub struct GrammarAST {
    pub start: Option<String>,
    pub rules: HashMap<String, Rule>,
    pub tokens: HashSet<String>,
    pub precs: HashMap<String, Precedence>
}

#[derive(Debug)]
pub struct Rule {
    pub name: String,
    pub productions: Vec<Production>
}

#[derive(Debug)]
pub struct Production {
    pub symbols: Vec<Symbol>,
    pub precedence: Option<String>
}

#[derive(Clone, Debug, Hash, Eq, PartialEq)]
pub enum Symbol {
    Nonterminal(String),
    Terminal(String)
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

/// GrammarAST validation errors return an instance of this struct.
#[derive(Debug)]
pub struct GrammarValidationError {
    pub kind: GrammarValidationErrorKind,
    pub sym: Option<Symbol>
}

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
            Symbol::Nonterminal(ref s) => write!(f, "{}", s),
            Symbol::Terminal(ref s)    => write!(f, "{}", s)
        }
    }
}

impl GrammarAST {
    pub fn new() -> GrammarAST {
        GrammarAST {
            start:   None,
            rules:   HashMap::new(),
            tokens:  HashSet::new(),
            precs:   HashMap::new(),
        }
    }

    pub fn add_prod(&mut self, key: String, syms: Vec<Symbol>, prec: Option<String>) {
        let rule = self.rules.entry(key.clone()).or_insert_with(|| Rule::new(key));
        rule.add_prod(syms, prec);
    }

    pub fn get_rule(&self, key: &str) -> Option<&Rule>{
        self.rules.get(key)
    }

    pub fn has_token(&self, s: &str) -> bool {
        self.tokens.contains(s)
    }

    /// Perform basic validation on the grammar, namely:
    ///   1) The start rule references a rule in the grammar
    ///   2) Every nonterminal reference references a rule in the grammar
    ///   3) Every terminal reference references a declared token
    ///   4) If a production has a precedence terminal, then it references a declared token
    /// If the validation succeeds, None is returned.
    pub fn validate(&self) -> Result<(), GrammarValidationError> {
        match self.start {
            None => return Err(GrammarValidationError{kind: GrammarValidationErrorKind::NoStartRule, sym: None}),
            Some(ref s) => {
                if !self.rules.contains_key(s) {
                    return Err(GrammarValidationError{kind: GrammarValidationErrorKind::InvalidStartRule,
                                               sym: Some(Symbol::Nonterminal(s.clone()))});
                }
            }
        }
        for rule in self.rules.values() {
            for prod in &rule.productions {
                if let Some(ref n) = prod.precedence {
                    if !self.tokens.contains(n) {
                        return Err(GrammarValidationError{kind: GrammarValidationErrorKind::UnknownToken,
                            sym: Some(Symbol::Terminal(n.clone()))});
                    }
                    if !self.precs.contains_key(n) {
                        return Err(GrammarValidationError{kind: GrammarValidationErrorKind::NoPrecForToken,
                            sym: Some(Symbol::Terminal(n.clone()))});
                    }
                }
                for sym in prod.symbols.iter() {
                    match *sym {
                        Symbol::Nonterminal(ref name) => {
                            if !self.rules.contains_key(name) {
                                return Err(GrammarValidationError{kind: GrammarValidationErrorKind::UnknownRuleRef,
                                    sym: Some(sym.clone())});
                            }
                        }
                        Symbol::Terminal(ref name) => {
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

impl PartialEq for Production {
    fn eq(&self, other: &Production) -> bool {
        self.symbols == other.symbols
    }
}

impl Rule {
    pub fn new(name: String) -> Rule {
        Rule {name: name, productions: vec![]}
    }

    pub fn add_prod(&mut self, syms: Vec<Symbol>, prec: Option<String>) {
        self.productions.push(Production{symbols: syms, precedence: prec});
    }
}

impl PartialEq for Rule {
    fn eq(&self, other: &Rule) -> bool {
        self.name == other.name && self.productions == other.productions
    }
}

#[cfg(test)]
mod test {
    use super::{GrammarAST, GrammarValidationError, GrammarValidationErrorKind, Symbol};
    use grammar::{AssocKind, Precedence};

    fn nonterminal(n: &str) -> Symbol {
        Symbol::Nonterminal(n.to_string())
    }

    fn terminal(n: &str) -> Symbol {
        Symbol::Terminal(n.to_string())
    }

    #[test]
    fn test_empty_grammar(){
        let grm = GrammarAST::new();
        match grm.validate() {
            Err(GrammarValidationError{kind: GrammarValidationErrorKind::NoStartRule, ..}) => (),
            _ => panic!("Validation error")
        }
    }

    #[test]
    fn test_invalid_start_rule(){
        let mut grm = GrammarAST::new();
        grm.start = Some("A".to_string());
        grm.add_prod("B".to_string(), vec!(), None);
        match grm.validate() {
            Err(GrammarValidationError{kind: GrammarValidationErrorKind::InvalidStartRule, ..}) => (),
            _ => panic!("Validation error")
        }
    }

    #[test]
    fn test_valid_start_rule(){
        let mut grm = GrammarAST::new();
        grm.start = Some("A".to_string());
        grm.add_prod("A".to_string(), vec!(), None);
        assert!(grm.validate().is_ok());
    }

    #[test]
    fn test_valid_nonterminal_ref(){
        let mut grm = GrammarAST::new();
        grm.start = Some("A".to_string());
        grm.add_prod("A".to_string(), vec!(nonterminal("B")), None);
        grm.add_prod("B".to_string(), vec!(), None);
        assert!(grm.validate().is_ok());
    }

    #[test]
    fn test_invalid_nonterminal_ref(){
        let mut grm = GrammarAST::new();
        grm.start = Some("A".to_string());
        grm.add_prod("A".to_string(), vec!(nonterminal("B")), None);
        match grm.validate() {
            Err(GrammarValidationError{kind: GrammarValidationErrorKind::UnknownRuleRef, ..}) => (),
            _ => panic!("Validation error")
        }
    }

    #[test]
    fn test_valid_terminal_ref(){
        let mut grm = GrammarAST::new();
        grm.tokens.insert("b".to_string());
        grm.start = Some("A".to_string());
        grm.add_prod("A".to_string(), vec!(terminal("b")), None);
        assert!(grm.validate().is_ok());
    }

    #[test]
    #[should_panic]
    fn test_valid_token_ref(){
        // for now we won't support the YACC feature that allows
        // to redefine nonterminals as tokens by adding them to '%token'
        let mut grm = GrammarAST::new();
        grm.tokens.insert("b".to_string());
        grm.start = Some("A".to_string());
        grm.add_prod("A".to_string(), vec!(nonterminal("b")), None);
        assert!(grm.validate().is_ok());
    }

    #[test]
    fn test_invalid_terminal_ref(){
        let mut grm = GrammarAST::new();
        grm.start = Some("A".to_string());
        grm.add_prod("A".to_string(), vec!(terminal("b")), None);
        match grm.validate() {
            Err(GrammarValidationError{kind: GrammarValidationErrorKind::UnknownToken, ..}) => (),
            _ => panic!("Validation error")
        }
    }

    #[test]
    fn test_invalid_nonterminal_forgotten_token(){
        let mut grm = GrammarAST::new();
        grm.start = Some("A".to_string());
        grm.add_prod("A".to_string(), vec!(nonterminal("b"), terminal("b")), None);
        match grm.validate() {
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
        grm.add_prod("A".to_string(), vec!(terminal("b")), Some("b".to_string()));
        assert!(grm.validate().is_ok());
    }

    #[test]
    fn test_invalid_precedence_override(){
        let mut grm = GrammarAST::new();
        grm.start = Some("A".to_string());
        grm.add_prod("A".to_string(), vec!(terminal("b")), Some("b".to_string()));
        match grm.validate() {
            Err(GrammarValidationError{kind: GrammarValidationErrorKind::UnknownToken, ..}) => (),
            _ => panic!("Validation error")
        }
        grm.tokens.insert("b".to_string());
        match grm.validate() {
            Err(GrammarValidationError{kind: GrammarValidationErrorKind::NoPrecForToken, ..}) => (),
            _ => panic!("Validation error")
        }
    }
}
