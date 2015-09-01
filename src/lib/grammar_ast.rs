use std::collections::{HashMap, HashSet};
use std::fmt;

pub struct GrammarAST {
    pub start: Option<String>,
    pub rules: HashMap<String, Rule>,
    pub tokens: HashSet<String>
}

pub struct Rule {
    pub name: String,
    pub alternatives: Vec<Vec<Symbol>>
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
                write!(f, "Start rule does not appear in grammar")
            },
            GrammarASTErrorKind::UnknownRuleRef => {
                write!(f, "Unknown reference to rule")
            },
            GrammarASTErrorKind::UnknownToken => {
                write!(f, "Unknown token")
            }
        }
    }
}

impl GrammarAST {
    pub fn new() -> GrammarAST {
        let hm = HashMap::new();
        let t = HashSet::new();
        GrammarAST {start: None, rules: hm, tokens: t}
    }

    pub fn add_rule(&mut self, key: String, value: Vec<Symbol>) {
        let rule = self.rules.entry(key.clone()).or_insert(Rule::new(key));
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
                    return Err(GrammarASTError{kind: GrammarASTErrorKind::InvalidStartRule, sym: None});
                }
            }
        }
        for rule in self.rules.values() {
            for alt in rule.alternatives.iter() {
                for sym in alt.iter() {
                    match sym {
                        &Symbol::Nonterminal(ref name) => {
                            if !self.rules.contains_key(name) {
                                return Err(GrammarASTError{kind: GrammarASTErrorKind::UnknownRuleRef,
                                    sym: Some(sym.clone())});
                            }
                        }
                        &Symbol::Terminal(ref name) => {
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
        Rule {name: name, alternatives: vec![]}
    }

    pub fn add_symbols(&mut self, v: Vec<Symbol>) {
        self.alternatives.push(v);
    }
}

impl fmt::Display for Rule {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        fmt.debug_struct("Rule")
           .field("name", &self.name)
           .field("alternatives", &self.alternatives)
           .finish()
    }
}

impl fmt::Debug for Rule {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        fmt.debug_struct("Rule")
           .field("name", &self.name)
           .field("alternatives", &self.alternatives)
           .finish()
    }
}

impl PartialEq for Rule {
    fn eq(&self, other: &Rule) -> bool {
        self.name == other.name && self.alternatives == other.alternatives
    }
}

/// Returns a nonterminal symbol with name `n`.
pub fn nonterminal(n: &str) -> Symbol {
    Symbol::Nonterminal(n.to_string())
}

/// Returns a terminal symbol with name `n`.
pub fn terminal(n: &str) -> Symbol {
    Symbol::Terminal(n.to_string())
}

