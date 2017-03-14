use std::collections::HashMap;
use std::slice::Iter;

use regex::Regex;

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

#[derive(Clone, Copy, Debug)]
pub struct Lexeme {
    pub tok_id: usize,
    /// Byte offset of the start of the lexeme
    pub start: usize,
    /// Length in bytes of the lexeme
    pub len: usize
}

#[derive(Debug)]
pub struct LexError {
    idx: usize
}

pub struct Lexer {
    rules: Vec<Rule>
}

impl Lexer {
    pub fn new(rules: Vec<Rule>) -> Lexer {
        Lexer {rules: rules}
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

    pub fn lex(&self, s: &str) -> Result<Vec<Lexeme>, LexError> {
        let mut i = 0; // byte index into s
        let mut lxs = Vec::new(); // lexemes

        while i < s.len() {
            let mut longest = 0; // Length of the longest match
            let mut longest_ridx = 0; // This is only valid iff longest != 0
            for (ridx, r) in self.iter_rules().enumerate() {
                if let Some(m) = r.re.find(&s[i..]) {
                    let len = m.end();
                    // Note that by using ">", we implicitly prefer an earlier over a later rule, if
                    // both match an input of the same length.
                    if len > longest {
                        longest = len;
                        longest_ridx = ridx;
                    }
                }
            }
            if longest > 0 {
                let r = &self.get_rule(longest_ridx).unwrap();
                if r.name.is_some() {
                    lxs.push(Lexeme{tok_id: r.tok_id, start: i, len: longest});
                }
                i += longest;
            } else {
                return Err(LexError{idx: i});
            }
        }
        Ok(lxs)
    }
}

#[cfg(test)]
mod test {
    use std::collections::HashMap;
    use super::*;
    use parser::parse_lex;

    #[test]
    fn test_basic() {
        let src = r"
%%
[0-9]+ int
[a-zA-Z]+ id
[ \t] ;
        ".to_string();
        let mut lexer = parse_lex(&src).unwrap();
        let mut map = HashMap::new();
        map.insert("int", 0);
        map.insert("id", 1);
        lexer.set_rule_ids(&map);

        let lexemes = lexer.lex("abc 123").unwrap();
        assert_eq!(lexemes.len(), 2);
        let lex1 = lexemes.get(0).unwrap();
        assert_eq!(lex1.tok_id, 1);
        assert_eq!(lex1.start, 0);
        assert_eq!(lex1.len, 3);
        let lex2 = lexemes.get(1).unwrap();
        assert_eq!(lex2.tok_id, 0);
        assert_eq!(lex2.start, 4);
        assert_eq!(lex2.len, 3);
    }

    #[test]
    fn test_basic_error() {
        let src = "
%%
[0-9]+ int
        ".to_string();
        let lexer = parse_lex(&src).unwrap();
        match lexer.lex("abc") {
            Ok(_)  => panic!("Invalid input lexed"),
            Err(LexError{idx: 0}) => (),
            Err(e) => panic!("Incorrect error returned {:?}", e)
        };
    }

    #[test]
    fn test_longest_match() {
        let src = "%%
if IF
[a-z]+ ID
[ ] ;".to_string();
        let mut lexer = parse_lex(&src).unwrap();
        let mut map = HashMap::new();
        map.insert("IF", 0);
        map.insert("ID", 1);
        lexer.set_rule_ids(&map);

        let lexemes = lexer.lex("iff if").unwrap();
        println!("{:?}", lexemes);
        assert_eq!(lexemes.len(), 2);
        let lex1 = lexemes.get(0).unwrap();
        assert_eq!(lex1.tok_id, 1);
        assert_eq!(lex1.start, 0);
        assert_eq!(lex1.len, 3);
        let lex2 = lexemes.get(1).unwrap();
        assert_eq!(lex2.tok_id, 0);
        assert_eq!(lex2.start, 4);
        assert_eq!(lex2.len, 2);
    }
}
