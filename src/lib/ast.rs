use std::collections::HashMap;
use regex::Regex;

pub struct LexAST {
    pub rules: Vec<Rule>
}

impl LexAST {
    pub fn new() -> LexAST {
        LexAST {rules: Vec::new()}
    }

    /// Appends a rule to the Vec of rules. Panics if a rule with the same name already exists.
    pub fn set_rule(&mut self, r: Rule) {
        assert!(r.name.is_none() || self.get_rule(&r.name.as_ref().unwrap()).is_none());
        self.rules.push(r);
    }

    /// Get the `Rule` instance associated with a particular name.
    pub fn get_rule(&self, n: &str) -> Option<&Rule> {
        self.rules.iter().find(|r| !r.name.is_none() && r.name.as_ref().unwrap() == n)
    }

    /// Set the id attribute on rules to the corresponding value in `map`. This is typically used
    /// to synchronise a parser's notion of token IDs with the lexers.
    pub fn set_rule_ids(&mut self, map: &HashMap<&str, usize>) {
        for r in self.rules.iter_mut() {
            match r.name.as_ref() {
                None => (),
                Some(n) => {
                    r.id = *map.get(&**n).unwrap()
                }
            };
        }
    }
}

pub struct Rule {
    /// The ID of this rule as set by the client/parser. Its initial value is usize::max_value().
    pub id: usize,
    /// This rule's name. If None, then text which matches this rule will be skipped (i.e. will not
    /// create a lexeme).
    pub name: Option<String>,
    pub re_str: String,
    pub re: Regex
}

