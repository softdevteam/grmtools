use std::collections::HashMap;
use std::slice::Iter;
use regex::Regex;

pub struct LexAST {
    rules: Vec<Rule>
}

impl LexAST {
    pub fn new() -> LexAST {
        LexAST {rules: Vec::new()}
    }

    /// Appends a rule to the Vec of rules. Panics if a rule with the same name already exists.
    pub fn set_rule(&mut self, r: Rule) {
        assert!(r.name.is_none() || self.get_rule_by_name(&r.name.as_ref().unwrap()).is_none());
        self.rules.push(r);
    }

    /// Get the `Rule` at index `idx`.
    pub fn get_rule(&self, idx: usize) -> Option<&Rule> {
        self.rules.get(idx)
    }

    /// Get the `Rule` instance associated with a particular token ID.
    pub fn get_rule_by_id(&self, tok_id: usize) -> Option<&Rule> {
        self.rules.iter().find(|r| r.tok_id == tok_id)
    }

    /// Get the `Rule` instance associated with a particular name.
    pub fn get_rule_by_name(&self, n: &str) -> Option<&Rule> {
        self.rules.iter().find(|r| !r.name.is_none() && r.name.as_ref().unwrap() == n)
    }

    /// Set the id attribute on rules to the corresponding value in `map`. This is typically used
    /// to synchronise a parser's notion of token IDs with the lexers.
    pub fn set_rule_ids(&mut self, map: &HashMap<&str, usize>) {
        for r in self.rules.iter_mut() {
            match r.name.as_ref() {
                None => (),
                Some(n) => {
                    r.tok_id = *map.get(&**n).unwrap()
                }
            };
        }
    }

    /// Returns an iterator over all rules in this AST.
    pub fn iter_rules(&self) -> Iter<Rule> {
        self.rules.iter()
    }
}

pub struct Rule {
    /// The ID that tokens created against this rule will be given. It is initially given a
    /// guaranteed unique value; that value can be overridden by clients.
    pub tok_id: usize,
    /// This rule's name. If None, then text which matches this rule will be skipped (i.e. will not
    /// create a lexeme).
    pub name: Option<String>,
    pub re_str: String,
    pub re: Regex
}

