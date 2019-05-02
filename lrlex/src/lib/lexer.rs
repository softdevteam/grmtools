// Copyright (c) 2017 King's College London
// created by the Software Development Team <http://soft-dev.org/>
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0>, or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, or the UPL-1.0 license <http://opensource.org/licenses/UPL>
// at your option. This file may not be copied, modified, or distributed except according to those
// terms.

use std::{
    collections::{HashMap, HashSet},
    hash::Hash,
    slice::Iter
};

use num_traits::{PrimInt, Unsigned};
use regex::{self, Regex, RegexBuilder};

use lrpar::{LexError, Lexeme, Lexer};

pub struct Rule<StorageT> {
    /// If `Some`, the ID that lexemes created against this rule will be given (lrlex gives such
    /// rules a guaranteed unique value, though that value can be overridden by clients who need to
    /// control the ID). If `None`, then this rule specifies lexemes which should not appear in the
    /// user's input.
    pub tok_id: Option<StorageT>,
    /// This rule's name. If None, then text which matches this rule will be skipped (i.e. will not
    /// create a lexeme).
    pub name: Option<String>,
    pub re_str: String,
    pub re: Regex
}

impl<StorageT> Rule<StorageT> {
    /// Create a new `Rule`. This interface is unstable and should only be used by code generated
    /// by lrlex itself.
    #[doc(hidden)]
    pub fn new(
        tok_id: Option<StorageT>,
        name: Option<String>,
        re_str: String
    ) -> Result<Rule<StorageT>, regex::Error> {
        let re = RegexBuilder::new(&format!("\\A(?:{})", &re_str))
            .multi_line(true)
            .dot_matches_new_line(true)
            .build()?;
        Ok(Rule {
            tok_id,
            name,
            re_str,
            re
        })
    }
}

/// This struct represents, in essence, a .l file in memory. From it one can produce a `Lexer`
/// which actually lexes inputs.
pub struct LexerDef<StorageT> {
    pub(crate) rules: Vec<Rule<StorageT>>
}

impl<StorageT: Copy + Eq + Hash + PrimInt + Unsigned> LexerDef<StorageT> {
    pub fn new(rules: Vec<Rule<StorageT>>) -> LexerDef<StorageT> {
        LexerDef { rules }
    }

    /// Get the `Rule` at index `idx`.
    pub fn get_rule(&self, idx: usize) -> Option<&Rule<StorageT>> {
        self.rules.get(idx)
    }

    /// Get the `Rule` instance associated with a particular lexeme ID. Panics if no such rule
    /// exists.
    pub fn get_rule_by_id(&self, tok_id: StorageT) -> &Rule<StorageT> {
        &self
            .rules
            .iter()
            .find(|r| r.tok_id == Some(tok_id))
            .unwrap()
    }

    /// Get the `Rule` instance associated with a particular name.
    pub fn get_rule_by_name(&self, n: &str) -> Option<&Rule<StorageT>> {
        self.rules
            .iter()
            .find(|r| r.name.as_ref().map(String::as_str) == Some(n))
    }

    /// Set the id attribute on rules to the corresponding value in `map`. This is typically used
    /// to synchronise a parser's notion of lexeme IDs with the lexers. While doing this, it keeps
    /// track of which lexemes:
    ///   1) are defined in the lexer but not referenced by the parser
    ///   2) and referenced by the parser but not defined in the lexer
    /// and returns them as a tuple `(Option<HashSet<&str>>, Option<HashSet<&str>>)` in the order
    /// (*defined_in_lexer_missing_from_parser*, *referenced_in_parser_missing_from_lexer*). Since
    /// in most cases both sets are expected to be empty, `None` is returned to avoid a `HashSet`
    /// allocation.
    ///
    /// Lexing and parsing can continue if either set is non-empty, so it is up to the caller as to
    /// what action they take if either return set is non-empty. A non-empty set #1 is often
    /// benign: some lexers deliberately define tokens which are not used (e.g. reserving future
    /// keywords). A non-empty set #2 is more likely to be an error since there are parts of the
    /// grammar where nothing the user can input will be parseable.
    pub fn set_rule_ids<'a>(
        &'a mut self,
        rule_ids_map: &HashMap<&'a str, StorageT>
    ) -> (Option<HashSet<&'a str>>, Option<HashSet<&'a str>>) {
        // Because we have to iter_mut over self.rules, we can't easily store a reference to the
        // rule's name at the same time. Instead, we store the index of each such rule and
        // recover the names later.
        let mut missing_from_parser_idxs = Vec::new();
        let mut rules_with_names = 0;
        for (i, r) in self.rules.iter_mut().enumerate() {
            if let Some(ref n) = r.name {
                match rule_ids_map.get(&**n) {
                    Some(tok_id) => r.tok_id = Some(*tok_id),
                    None => {
                        r.tok_id = None;
                        missing_from_parser_idxs.push(i);
                    }
                }
                rules_with_names += 1;
            }
        }

        let missing_from_parser;
        if missing_from_parser_idxs.is_empty() {
            missing_from_parser = None;
        } else {
            let mut mfp = HashSet::with_capacity(missing_from_parser_idxs.len());
            for i in &missing_from_parser_idxs {
                mfp.insert(self.rules[*i].name.as_ref().unwrap().as_str());
            }
            missing_from_parser = Some(mfp);
        };

        let missing_from_lexer;
        if rules_with_names - missing_from_parser_idxs.len() == rule_ids_map.len() {
            missing_from_lexer = None
        } else {
            missing_from_lexer = Some(
                rule_ids_map
                    .keys()
                    .cloned()
                    .collect::<HashSet<&str>>()
                    .difference(
                        &self
                            .rules
                            .iter()
                            .filter(|x| x.name.is_some())
                            .map(|x| &**x.name.as_ref().unwrap())
                            .collect::<HashSet<&str>>()
                    )
                    .cloned()
                    .collect::<HashSet<&str>>()
            );
        }

        (missing_from_lexer, missing_from_parser)
    }

    /// Returns an iterator over all rules in this AST.
    pub fn iter_rules(&self) -> Iter<Rule<StorageT>> {
        self.rules.iter()
    }

    /// Return a lexer for the `String` `s` that will lex relative to this `LexerDef`.
    pub fn lexer<'a>(&'a self, s: &'a str) -> impl Lexer<StorageT> + 'a {
        LRLexer::new(self, s)
    }
}

/// A lexer holds a reference to a string and can lex it into `Lexeme`s. Although the struct is
/// tied to a single string, no guarantees are made about whether the lexemes are cached or not.
pub struct LRLexer<'a, StorageT> {
    lexerdef: &'a LexerDef<StorageT>,
    s: &'a str,
    i: usize,
    newlines: Vec<usize>
}

impl<'a, StorageT: Copy + Eq> LRLexer<'a, StorageT> {
    fn new(lexerdef: &'a LexerDef<StorageT>, s: &'a str) -> LRLexer<'a, StorageT> {
        LRLexer {
            lexerdef,
            s,
            i: 0,
            newlines: Vec::new()
        }
    }
}

impl<'a, StorageT: Copy + Eq + Hash + PrimInt + Unsigned> Lexer<StorageT>
    for LRLexer<'a, StorageT>
{
    fn next(&mut self) -> Option<Result<Lexeme<StorageT>, LexError>> {
        while self.i < self.s.len() {
            let old_i = self.i;
            let mut longest = 0; // Length of the longest match
            let mut longest_ridx = 0; // This is only valid iff longest != 0
            for (ridx, r) in self.lexerdef.iter_rules().enumerate() {
                if let Some(m) = r.re.find(&self.s[old_i..]) {
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
                self.newlines.extend(
                    self.s[old_i..old_i + longest]
                        .chars()
                        .enumerate()
                        .filter(|&(_, c)| c == '\n')
                        .map(|(j, _)| old_i + j + 1)
                );
                let r = &self.lexerdef.get_rule(longest_ridx).unwrap();
                if r.name.is_some() {
                    match r.tok_id {
                        Some(tok_id) => {
                            self.i += longest;
                            return Some(Ok(Lexeme::new(tok_id, old_i, Some(longest))));
                        }
                        None => {
                            self.i = self.s.len();
                            return Some(Err(LexError { idx: old_i }));
                        }
                    }
                }
                self.i += longest;
            } else {
                self.i = self.s.len();
                return Some(Err(LexError { idx: old_i }));
            }
        }
        None
    }

    fn line_col(&self, i: usize) -> (usize, usize) {
        if i > self.s.len() {
            panic!("Offset {} exceeds known input length {}", i, self.s.len());
        }

        fn line_col_off<StorageT>(lexer: &LRLexer<StorageT>, i: usize) -> (usize, usize) {
            if lexer.newlines.is_empty() || i < lexer.newlines[0] {
                return (1, i);
            }

            for j in 0..lexer.newlines.len() - 1 {
                if lexer.newlines[j + 1] > i {
                    return (j + 2, i - lexer.newlines[j]);
                }
            }
            (
                lexer.newlines.len() + 1,
                i - lexer.newlines[lexer.newlines.len() - 1]
            )
        }

        let (line_idx, col_byte) = line_col_off(self, i);
        let line = self.surrounding_line_str(i);
        (line_idx, line[..col_byte].chars().count() + 1)
    }

    fn surrounding_line_str(&self, i: usize) -> &str {
        fn surrounding_line_off<StorageT>(lexer: &LRLexer<StorageT>, i: usize) -> (usize, usize) {
            if i > lexer.s.len() {
                panic!("Offset {} exceeds known input length {}", i, lexer.s.len());
            }

            if lexer.newlines.is_empty() {
                return (0, lexer.s.len());
            } else if i < lexer.newlines[0] {
                return (0, lexer.newlines[0] - 1);
            }

            for j in 0..lexer.newlines.len() - 1 {
                if lexer.newlines[j + 1] > i {
                    return (lexer.newlines[j], lexer.newlines[j + 1] - 1);
                }
            }
            (lexer.newlines[lexer.newlines.len() - 1], lexer.s.len())
        }

        let (st, en) = surrounding_line_off(self, i);
        &self.s[st..en]
    }

    fn lexeme_str(&self, l: &Lexeme<StorageT>) -> &str {
        &self.s[l.start()..l.end()]
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::parser::parse_lex;
    use std::collections::HashMap;

    #[test]
    fn test_basic() {
        let src = r"
%%
[0-9]+ 'int'
[a-zA-Z]+ 'id'
[ \t] ;
        "
        .to_string();
        let mut lexer = parse_lex(&src).unwrap();
        let mut map = HashMap::new();
        map.insert("int", 0);
        map.insert("id", 1);
        assert_eq!(lexer.set_rule_ids(&map), (None, None));

        let lexemes = lexer.lexer(&"abc 123").all_lexemes().unwrap();
        assert_eq!(lexemes.len(), 2);
        let lex1 = lexemes[0];
        assert_eq!(lex1.tok_id(), 1u8);
        assert_eq!(lex1.start(), 0);
        assert_eq!(lex1.len(), 3);
        let lex2 = lexemes[1];
        assert_eq!(lex2.tok_id(), 0);
        assert_eq!(lex2.start(), 4);
        assert_eq!(lex2.len(), 3);
    }

    #[test]
    fn test_basic_error() {
        let src = "
%%
[0-9]+ 'int'
        "
        .to_string();
        let lexer = parse_lex::<u8>(&src).unwrap();
        match lexer.lexer(&"abc").all_lexemes() {
            Ok(_) => panic!("Invalid input lexed"),
            Err(LexError { idx: 0 }) => (),
            Err(e) => panic!("Incorrect error returned {:?}", e)
        };
    }

    #[test]
    fn test_longest_match() {
        let src = "%%
if 'IF'
[a-z]+ 'ID'
[ ] ;"
            .to_string();
        let mut lexer = parse_lex(&src).unwrap();
        let mut map = HashMap::new();
        map.insert("IF", 0);
        map.insert("ID", 1);
        assert_eq!(lexer.set_rule_ids(&map), (None, None));

        let lexemes = lexer.lexer(&"iff if").all_lexemes().unwrap();
        assert_eq!(lexemes.len(), 2);
        let lex1 = lexemes[0];
        assert_eq!(lex1.tok_id(), 1u8);
        assert_eq!(lex1.start(), 0);
        assert_eq!(lex1.len(), 3);
        let lex2 = lexemes[1];
        assert_eq!(lex2.tok_id(), 0);
        assert_eq!(lex2.start(), 4);
        assert_eq!(lex2.len(), 2);
    }

    #[test]
    fn test_multibyte() {
        let src = "%%
[a❤]+ 'ID'
[ ] ;"
            .to_string();
        let mut lexerdef = parse_lex(&src).unwrap();
        let mut map = HashMap::new();
        map.insert("ID", 0u8);
        assert_eq!(lexerdef.set_rule_ids(&map), (None, None));

        let mut lexer = lexerdef.lexer("a ❤ a");
        let lexemes = lexer.all_lexemes().unwrap();
        assert_eq!(lexemes.len(), 3);
        let lex1 = lexemes[0];
        assert_eq!(lex1.start(), 0);
        assert_eq!(lex1.len(), 1);
        assert_eq!(lexer.lexeme_str(&lex1), "a");
        let lex2 = lexemes[1];
        assert_eq!(lex2.start(), 2);
        assert_eq!(lex2.len(), 3);
        assert_eq!(lexer.lexeme_str(&lex2), "❤");
        let lex3 = lexemes[2];
        assert_eq!(lex3.start(), 6);
        assert_eq!(lex3.len(), 1);
        assert_eq!(lexer.lexeme_str(&lex3), "a");
    }

    #[test]
    fn test_line_col() {
        let src = "%%
[a-z]+ 'ID'
[ \\n] ;"
            .to_string();
        let mut lexerdef = parse_lex(&src).unwrap();
        let mut map = HashMap::new();
        map.insert("ID", 0u8);
        assert_eq!(lexerdef.set_rule_ids(&map), (None, None));

        let mut lexer = lexerdef.lexer("a b c");
        let lexemes = lexer.all_lexemes().unwrap();
        assert_eq!(lexemes.len(), 3);
        assert_eq!(lexer.line_col(lexemes[1].start()), (1, 3));
        assert_eq!(lexer.surrounding_line_str(lexemes[1].start()), "a b c");

        let mut lexer = lexerdef.lexer("a b c\n");
        let lexemes = lexer.all_lexemes().unwrap();
        assert_eq!(lexemes.len(), 3);
        assert_eq!(lexer.line_col(lexemes[1].start()), (1, 3));
        assert_eq!(lexer.surrounding_line_str(lexemes[1].start()), "a b c");

        let mut lexer = lexerdef.lexer(" a\nb\n  c d");
        let lexemes = lexer.all_lexemes().unwrap();
        assert_eq!(lexemes.len(), 4);
        assert_eq!(lexer.line_col(lexemes[0].start()), (1, 2));
        assert_eq!(lexer.line_col(lexemes[1].start()), (2, 1));
        assert_eq!(lexer.line_col(lexemes[2].start()), (3, 3));
        assert_eq!(lexer.line_col(lexemes[3].start()), (3, 5));
        assert_eq!(lexer.surrounding_line_str(lexemes[0].start()), " a");
        assert_eq!(lexer.surrounding_line_str(lexemes[1].start()), "b");
        assert_eq!(lexer.surrounding_line_str(lexemes[2].start()), "  c d");
        assert_eq!(lexer.surrounding_line_str(lexemes[3].start()), "  c d");
    }

    #[test]
    fn test_line_col_multibyte() {
        let src = "%%
[a-z❤]+ 'ID'
[ \\n] ;"
            .to_string();
        let mut lexerdef = parse_lex(&src).unwrap();
        let mut map = HashMap::new();
        map.insert("ID", 0u8);
        assert_eq!(lexerdef.set_rule_ids(&map), (None, None));

        let mut lexer = lexerdef.lexer(" a\n❤ b");
        let lexemes = lexer.all_lexemes().unwrap();
        assert_eq!(lexemes.len(), 3);
        assert_eq!(lexer.line_col(lexemes[0].start()), (1, 2));
        assert_eq!(lexer.line_col(lexemes[1].start()), (2, 1));
        assert_eq!(lexer.line_col(lexemes[2].start()), (2, 3));
        assert_eq!(lexer.surrounding_line_str(lexemes[0].start()), " a");
        assert_eq!(lexer.surrounding_line_str(lexemes[1].start()), "❤ b");
        assert_eq!(lexer.surrounding_line_str(lexemes[2].start()), "❤ b");
    }

    #[test]
    #[should_panic]
    fn test_bad_line_col() {
        let src = "%%
[a-z]+ 'ID'
[ \\n] ;"
            .to_string();
        let mut lexerdef = parse_lex(&src).unwrap();
        let mut map = HashMap::new();
        map.insert("ID", 0u8);
        assert_eq!(lexerdef.set_rule_ids(&map), (None, None));

        let lexer = lexerdef.lexer("a b c");

        lexer.line_col(100);
    }

    #[test]
    fn test_missing_from_lexer_and_parser() {
        let src = "%%
[a-z]+ 'ID'
[ \\n] ;"
            .to_string();
        let mut lexerdef = parse_lex(&src).unwrap();
        let mut map = HashMap::new();
        map.insert("INT", 0u8);
        let mut missing_from_lexer = HashSet::new();
        missing_from_lexer.insert("INT");
        let mut missing_from_parser = HashSet::new();
        missing_from_parser.insert("ID");
        assert_eq!(
            lexerdef.set_rule_ids(&map),
            (Some(missing_from_lexer), Some(missing_from_parser))
        );

        match lexerdef.lexer(&" a ").all_lexemes() {
            Ok(_) => panic!("Invalid input lexed"),
            Err(LexError { idx: 1 }) => (),
            Err(e) => panic!("Incorrect error returned {:?}", e)
        };
    }
}
