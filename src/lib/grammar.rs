use std::collections::{HashMap, HashSet};
use std::fmt;

pub struct Grammar {
    pub start: String,
    pub rules: HashMap<String, Rule>,
    pub tokens: HashSet<String>
}

impl Grammar {
    pub fn new() -> Grammar {
        let s = String::new();
        let hm = HashMap::new();
        let t = HashSet::new();
        Grammar {start: s, rules: hm, tokens: t}
    }

    pub fn add_rule(&mut self, key: String, value: Vec<Symbol>) {
        let rule = self.rules.entry(key.clone()).or_insert(Rule::new(key));
        rule.add_symbols(value);
    }

    pub fn get_rule(&mut self, key: &str) -> Option<&Rule>{
        self.rules.get(key)
    }

    pub fn get_start(&mut self) -> &str {
        &self.start
    }

    pub fn has_token(&mut self, s: &str) -> bool{
        self.tokens.contains(s)
    }
}

impl fmt::Debug for Grammar {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        let mut s = String::new();
        s.push_str("Grammar:\n");
        s.push_str(&format!("   start: {}\n", &self.start));
        s.push_str(&format!("   tokens: {:?}\n", &self.tokens));
        for rule in &self.rules {
            s.push_str(&format!("   rule: {:?}\n", &rule));
        }
        writeln!(fmt, "{}", s)
    }
}

pub struct Rule {
    pub name: String,
    pub symbols: Vec<Vec<Symbol>>
}

impl Rule {
    pub fn new(name: String) -> Rule{
        Rule {name: name, symbols: vec![]}
    }

    pub fn add_symbols(&mut self, v: Vec<Symbol>) {
        self.symbols.push(v);
    }
}

impl fmt::Display for Rule {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        fmt.debug_struct("Rule")
           .field("name", &self.name)
           .field("symbols", &self.symbols)
           .finish()
    }
}

impl fmt::Debug for Rule {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        fmt.debug_struct("Rule")
           .field("name", &self.name)
           .field("symbols", &self.symbols)
           .finish()
    }
}

impl PartialEq for Rule {
    fn eq(&self, other: &Rule) -> bool {
        self.name == other.name && self.symbols == other.symbols
    }
}


#[derive(PartialEq)]
pub enum SymbolType {
    Terminal,
    Nonterminal,
    Epsilon
}

pub struct Symbol {
    pub name: String,
    pub typ: SymbolType
}

impl Symbol {
    pub fn new(s: String, t: SymbolType) -> Symbol {
        Symbol {name: s, typ: t}
    }
}

impl PartialEq for Symbol {
    fn eq(&self, other: &Symbol) -> bool {
        self.name == other.name && self.typ == other.typ
    }
}

impl fmt::Debug for Symbol {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
            let mut classname = String::new();
            match self.typ {
                SymbolType::Nonterminal => classname.push_str("Nonterminal"),
                SymbolType::Terminal => classname.push_str("Terminal"),
                SymbolType::Epsilon => classname.push_str("Epislon")
            }
            fmt.debug_struct(&classname)
                .field("name", &self.name)
                .finish()
    }
}
