use std::collections::HashMap;
use std::convert::TryFrom;
use std::slice::Iter;

use regex::Regex;

pub struct Rule<TokId> {
    /// The ID that tokens created against this rule will be given. It is initially given a
    /// guaranteed unique value; that value can be overridden by clients.
    pub tok_id: TokId,
    /// This rule's name. If None, then text which matches this rule will be skipped (i.e. will not
    /// create a lexeme).
    pub name: Option<String>,
    pub re_str: String,
    pub re: Regex
}

#[derive(Debug)]
pub struct LexError {
    idx: usize
}

pub struct Lexer<TokId> {
    rules: Vec<Rule<TokId>>
}

impl<TokId: Copy + Eq> Lexer<TokId> {
    pub fn new(rules: Vec<Rule<TokId>>) -> Lexer<TokId> {
        Lexer {rules: rules}
    }

    /// Get the `Rule` at index `idx`.
    pub fn get_rule(&self, idx: usize) -> Option<&Rule<TokId>> {
        self.rules.get(idx)
    }

    /// Get the `Rule` instance associated with a particular token ID.
    pub fn get_rule_by_id(&self, tok_id: TokId) -> Option<&Rule<TokId>> {
        self.rules.iter().find(|r| r.tok_id == tok_id)
    }

    /// Get the `Rule` instance associated with a particular name.
    pub fn get_rule_by_name(&self, n: &str) -> Option<&Rule<TokId>> {
        self.rules.iter().find(|r| !r.name.is_none() && r.name.as_ref().unwrap() == n)
    }

    /// Set the id attribute on rules to the corresponding value in `map`. This is typically used
    /// to synchronise a parser's notion of token IDs with the lexers.
    pub fn set_rule_ids(&mut self, map: &HashMap<&str, TokId>) {
        for r in self.rules.iter_mut() {
            match r.name.as_ref() {
                None => (),
                Some(n) => {
                    r.tok_id = map[&**n]
                }
            };
        }
    }

    /// Returns an iterator over all rules in this AST.
    pub fn iter_rules(&self) -> Iter<Rule<TokId>> {
        self.rules.iter()
    }

    pub fn lex(&self, s: &str) -> Result<Vec<Lexeme<TokId>>, LexError> {
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
                    lxs.push(Lexeme::new(r.tok_id, i, longest));
                }
                i += longest;
            } else {
                return Err(LexError{idx: i});
            }
        }
        Ok(lxs)
    }
}

#[derive(Clone, Copy, Debug)]
pub struct Lexeme<TokId> {
    start: usize,
    len: u32,
    tok_id: TokId
}

impl<TokId: Copy> Lexeme<TokId> {
    pub fn new(tok_id: TokId, start: usize, len: usize) -> Lexeme<TokId> {
        Lexeme{
            start: start,
            len: u32::try_from(len).unwrap(),
            tok_id: tok_id
        }
    }

    /// The token ID.
    pub fn tok_id(&self) -> TokId {
        self.tok_id
    }

    /// Byte offset of the start of the lexeme
    pub fn start(&self) -> usize {
        self.start
    }

    /// Length in bytes of the lexeme
    pub fn len(&self) -> usize {
        self.len as usize
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
        let lex1 = lexemes[0];
        assert_eq!(lex1.tok_id, 1);
        assert_eq!(lex1.start, 0);
        assert_eq!(lex1.len, 3);
        let lex2 = lexemes[1];
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
        let lexer = parse_lex::<u8>(&src).unwrap();
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
        let lex1 = lexemes[0];
        assert_eq!(lex1.tok_id, 1);
        assert_eq!(lex1.start, 0);
        assert_eq!(lex1.len, 3);
        let lex2 = lexemes[1];
        assert_eq!(lex2.tok_id, 0);
        assert_eq!(lex2.start, 4);
        assert_eq!(lex2.len, 2);
    }
}
