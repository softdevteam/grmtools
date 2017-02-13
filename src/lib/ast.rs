use std::collections::{HashMap, HashSet};
use std::fmt;

use grammar::Precedence;

pub struct GrammarAST {
    pub start: Option<String>,
    pub rules: HashMap<String, Rule>,
    pub tokens: HashSet<String>,
    pub precs: HashMap<String, Precedence>
}

pub struct Rule {
    pub name: String,
    pub productions: Vec<Vec<Symbol>>
}

#[derive(Clone, Debug, Hash, Eq, PartialEq)]
pub enum Symbol {
    Nonterminal(String),
    Terminal(String)
}

/// The various different possible grammar validation errors.
#[derive(Debug)]
pub enum GrammarASTErrorKind {
    NoStartRule,
    InvalidStartRule,
    UnknownRuleRef,
    UnknownToken
}

/// GrammarAST validation errors return an instance of this struct.
#[derive(Debug)]
pub struct GrammarASTError {
    pub kind: GrammarASTErrorKind,
    pub sym: Option<Symbol>
}

impl fmt::Display for GrammarASTError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.kind {
            GrammarASTErrorKind::NoStartRule => {
                write!(f, "No start rule specified")
            },
            GrammarASTErrorKind::InvalidStartRule => {
                write!(f, "Start rule '{}' does not appear in grammar", self.sym.as_ref().unwrap())
            },
            GrammarASTErrorKind::UnknownRuleRef => {
                write!(f, "Unknown reference to rule '{}'", self.sym.as_ref().unwrap())
            },
            GrammarASTErrorKind::UnknownToken => {
                write!(f, "Unknown token '{}'", self.sym.as_ref().unwrap())
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

    pub fn add_rule(&mut self, key: String, value: Vec<Symbol>) {
        let rule = self.rules.entry(key.clone()).or_insert_with(|| Rule::new(key));
        rule.add_symbols(value);
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
    /// If the validation succeeds, None is returned.
    pub fn validate(&self) -> Result<(), GrammarASTError> {
        match self.start {
            None => return Err(GrammarASTError{kind: GrammarASTErrorKind::NoStartRule, sym: None}),
            Some(ref s) => {
                if !self.rules.contains_key(s) {
                    return Err(GrammarASTError{kind: GrammarASTErrorKind::InvalidStartRule,
                                               sym: Some(Symbol::Nonterminal(s.clone()))});
                }
            }
        }
        for rule in self.rules.values() {
            for alt in &rule.productions {
                for sym in alt.iter() {
                    match *sym {
                        Symbol::Nonterminal(ref name) => {
                            if !self.rules.contains_key(name) {
                                return Err(GrammarASTError{kind: GrammarASTErrorKind::UnknownRuleRef,
                                    sym: Some(sym.clone())});
                            }
                        }
                        Symbol::Terminal(ref name) => {
                            if !self.tokens.contains(name) {
                                return Err(GrammarASTError{kind: GrammarASTErrorKind::UnknownToken,
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

impl fmt::Debug for GrammarAST {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        let mut s = String::new();
        s.push_str("GrammarAST:\n");
        s.push_str(&format!("   start: {:?}\n", &self.start));
        s.push_str(&format!("   tokens: {:?}\n", &self.tokens));
        for rule in &self.rules {
            s.push_str(&format!("   rule: {:?}\n", &rule));
        }
        writeln!(fmt, "{}", s)
    }
}

impl Rule {
    pub fn new(name: String) -> Rule {
        Rule {name: name, productions: vec![]}
    }

    pub fn add_symbols(&mut self, v: Vec<Symbol>) {
        self.productions.push(v);
    }
}

impl fmt::Display for Rule {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        fmt.debug_struct("Rule")
           .field("name", &self.name)
           .field("productions", &self.productions)
           .finish()
    }
}

impl fmt::Debug for Rule {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        fmt.debug_struct("Rule")
           .field("name", &self.name)
           .field("productions", &self.productions)
           .finish()
    }
}

impl PartialEq for Rule {
    fn eq(&self, other: &Rule) -> bool {
        self.name == other.name && self.productions == other.productions
    }
}

#[cfg(test)]
mod test {
    use super::{GrammarAST, GrammarASTError, GrammarASTErrorKind, Symbol};

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
            Err(GrammarASTError{kind: GrammarASTErrorKind::NoStartRule, ..}) => (),
            _ => panic!("Validation error")
        }
    }

    #[test]
    fn test_invalid_start_rule(){
        let mut grm = GrammarAST::new();
        grm.start = Some("A".to_string());
        grm.add_rule("B".to_string(), vec!());
        match grm.validate() {
            Err(GrammarASTError{kind: GrammarASTErrorKind::InvalidStartRule, ..}) => (),
            _ => panic!("Validation error")
        }
    }

    #[test]
    fn test_valid_start_rule(){
        let mut grm = GrammarAST::new();
        grm.start = Some("A".to_string());
        grm.add_rule("A".to_string(), vec!());
        assert!(grm.validate().is_ok());
    }

    #[test]
    fn test_valid_nonterminal_ref(){
        let mut grm = GrammarAST::new();
        grm.start = Some("A".to_string());
        grm.add_rule("A".to_string(), vec!(nonterminal("B")));
        grm.add_rule("B".to_string(), vec!());
        assert!(grm.validate().is_ok());
    }

    #[test]
    fn test_invalid_nonterminal_ref(){
        let mut grm = GrammarAST::new();
        grm.start = Some("A".to_string());
        grm.add_rule("A".to_string(), vec!(nonterminal("B")));
        match grm.validate() {
            Err(GrammarASTError{kind: GrammarASTErrorKind::UnknownRuleRef, ..}) => (),
            _ => panic!("Validation error")
        }
    }

    #[test]
    fn test_valid_terminal_ref(){
        let mut grm = GrammarAST::new();
        grm.tokens.insert("b".to_string());
        grm.start = Some("A".to_string());
        grm.add_rule("A".to_string(), vec!(terminal("b")));
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
        grm.add_rule("A".to_string(), vec!(nonterminal("b")));
        assert!(grm.validate().is_ok());
    }

    #[test]
    fn test_invalid_terminal_ref(){
        let mut grm = GrammarAST::new();
        grm.start = Some("A".to_string());
        grm.add_rule("A".to_string(), vec!(terminal("b")));
        match grm.validate() {
            Err(GrammarASTError{kind: GrammarASTErrorKind::UnknownToken, ..}) => (),
            _ => panic!("Validation error")
        }
    }

    #[test]
    fn test_invalid_nonterminal_forgotten_token(){
        let mut grm = GrammarAST::new();
        grm.start = Some("A".to_string());
        grm.add_rule("A".to_string(), vec!(nonterminal("b"), terminal("b")));
        match grm.validate() {
            Err(GrammarASTError{kind: GrammarASTErrorKind::UnknownRuleRef, ..}) => (),
            _ => panic!("Validation error")
        }
    }
}
