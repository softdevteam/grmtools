// Copyright (c) 2017 King's College London
// created by the Software Development Team <http://soft-dev.org/>
//
// The Universal Permissive License (UPL), Version 1.0
//
// Subject to the condition set forth below, permission is hereby granted to any person obtaining a
// copy of this software, associated documentation and/or data (collectively the "Software"), free
// of charge and under any and all copyright rights in the Software, and any and all patent rights
// owned or freely licensable by each licensor hereunder covering either (i) the unmodified
// Software as contributed to or provided by such licensor, or (ii) the Larger Works (as defined
// below), to deal in both
//
// (a) the Software, and
// (b) any piece of software and/or hardware listed in the lrgrwrks.txt file
// if one is included with the Software (each a "Larger Work" to which the Software is contributed
// by such licensors),
//
// without restriction, including without limitation the rights to copy, create derivative works
// of, display, perform, and distribute the Software and make, use, sell, offer for sale, import,
// export, have made, and have sold the Software and the Larger Work(s), and to sublicense the
// foregoing rights on either these or other terms.
//
// This license is subject to the following condition: The above copyright notice and either this
// complete permission notice or at a minimum a reference to the UPL must be included in all copies
// or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING
// BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
// NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
// DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::convert::TryFrom;
use std::rc::Rc;
use std::slice::Iter;

use regex::Regex;

pub struct Rule<TokId> {
    /// If `Some`, the ID that tokens created against this rule will be given (lrlex gives such
    /// rules a guaranteed unique value, though that value can be overridden by clients who need to
    /// control the ID). If `None`, then this rule specifies lexemes which should not appear in the
    /// user's input.
    pub tok_id: Option<TokId>,
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

/// This struct represents, in essence, a .l file in memory. From it one can produce a `Lexer`
/// which actually lexes inputs.
pub struct LexerDef<TokId> {
    rules: Vec<Rule<TokId>>
}

impl<TokId: Copy + Eq> LexerDef<TokId> {
    pub fn new(rules: Vec<Rule<TokId>>) -> LexerDef<TokId> {
        LexerDef{rules: rules}
    }

    /// Get the `Rule` at index `idx`.
    pub fn get_rule(&self, idx: usize) -> Option<&Rule<TokId>> {
        self.rules.get(idx)
    }

    /// Get the `Rule` instance associated with a particular token ID. Panics if no such rule
    /// exists.
    pub fn get_rule_by_id(&self, tok_id: TokId) -> &Rule<TokId> {
        &self.rules.iter().find(|r| r.tok_id == Some(tok_id)).unwrap()
    }

    /// Get the `Rule` instance associated with a particular name.
    pub fn get_rule_by_name(&self, n: &str) -> Option<&Rule<TokId>> {
        self.rules.iter().find(|r| !r.name.is_none() && r.name.as_ref().unwrap() == n)
    }

    /// Set the id attribute on rules to the corresponding value in `map`. This is typically used
    /// to synchronise a parser's notion of token IDs with the lexers. While doing this, it keeps
    /// track of which tokens:
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
    pub fn set_rule_ids<'a>(&'a mut self, map: &HashMap<&'a str, TokId>)
                            -> (Option<HashSet<&'a str>>, Option<HashSet<&'a str>>) {
        // Because we have to iter_mut over self.rules, we can't easily store a reference to the
        // rule's name at the same time. Instead, we store the index of each such rule and
        // recover the names later.
        let mut missing_from_parser_idxs = Vec::new();
        let mut rules_with_names = 0;
        for (i, r) in self.rules.iter_mut().enumerate() {
            match r.name.as_ref() {
                None => (),
                Some(n) => {
                    let nr = &**n;
                    match map.get(nr) {
                        Some(tok_id) => {
                            r.tok_id = Some(*tok_id);
                        }
                        None => {
                            r.tok_id = None;
                            missing_from_parser_idxs.push(i);
                        }
                    }
                    rules_with_names += 1;
                }
            }
        }

        let missing_from_parser;
        if missing_from_parser_idxs.is_empty() {
            missing_from_parser = None;
        } else {
            let mut mfp = HashSet::with_capacity(missing_from_parser_idxs.len());
            for i in missing_from_parser_idxs.iter() {
                mfp.insert(self.rules[*i].name.as_ref().unwrap().as_str());
            }
            missing_from_parser = Some(mfp);
        };

        let missing_from_lexer;
        if rules_with_names - missing_from_parser_idxs.len() == map.len() {
            missing_from_lexer = None
        } else {
            missing_from_lexer = Some(map.keys()
                                         .cloned()
                                         .collect::<HashSet<&str>>()
                                         .difference(&self.rules
                                                          .iter()
                                                          .filter(|x| x.name.is_some())
                                                          .map(|x| &**x.name.as_ref().unwrap())
                                                          .collect::<HashSet<&str>>())
                                         .cloned()
                                         .collect::<HashSet<&str>>());
        }

        (missing_from_lexer, missing_from_parser)
    }

    /// Returns an iterator over all rules in this AST.
    pub fn iter_rules(&self) -> Iter<Rule<TokId>> {
        self.rules.iter()
    }

    /// Return a lexer for the `String` `s` that will lex relative to this `LexerDef`.
    pub fn lexer<'a>(&'a self, s: &'a str) -> Lexer<'a, TokId> {
        Lexer::new(self, s)
    }
}

/// A lexer holds a reference to a string and can lex it into `Lexeme`s. Although the struct is
/// tied to a single string, no guarantees are made about whether the lexemes are cached or not.
pub struct Lexer<'a, TokId: 'a> {
    lexerdef: &'a LexerDef<TokId>,
    s: &'a str,
    newlines: Rc<RefCell<Vec<usize>>>
}

impl<'a, TokId: Copy + Eq> Lexer<'a, TokId> {
    fn new(lexerdef: &'a LexerDef<TokId>, s: &'a str) -> Lexer<'a, TokId> {
        Lexer {lexerdef, s, newlines: Rc::new(RefCell::new(Vec::new()))}
    }

    /// Return all this lexer's lexemes or a `LexError` if there was a problem when lexing.
    pub fn lexemes(&self) -> Result<Vec<Lexeme<TokId>>, LexError> {
        let mut i = 0; // byte index into s
        let mut lxs = Vec::new(); // lexemes

        while i < self.s.len() {
            let mut longest = 0; // Length of the longest match
            let mut longest_ridx = 0; // This is only valid iff longest != 0
            for (ridx, r) in self.lexerdef.iter_rules().enumerate() {
                if let Some(m) = r.re.find(&self.s[i..]) {
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
                self.newlines.borrow_mut().extend(self.s[i .. i + longest]
                                                      .chars()
                                                      .enumerate()
                                                      .filter(|&(_, c)| c == '\n')
                                                      .map(|(j, _)| i + j + 1));
                let r = &self.lexerdef.get_rule(longest_ridx).unwrap();
                if r.name.is_some() {
                    match r.tok_id {
                        Some(tok_id) => lxs.push(Lexeme::new(tok_id, i, longest)),
                        None => return Err(LexError{idx: i})
                    }
                }
                i += longest;
            } else {
                return Err(LexError{idx: i});
            }
        }
        Ok(lxs)
    }

    /// Return the line and column number of a `Lexeme`, or `Err` if it is clearly out of bounds
    /// for this lexer.
    pub fn line_and_col(&self, l: &Lexeme<TokId>) -> Result<(usize, usize), ()> {
        if l.start > self.s.len() {
            return Err(());
        }

        let newlines = self.newlines.borrow();
        if newlines.len() == 0 || l.start < newlines[0] {
            return Ok((1, l.start + 1));
        }

        for i in 0..newlines.len() - 1 {
            if newlines[i + 1] > l.start {
                return Ok((i + 2, l.start - newlines[i] + 1));
            }
        }
        Ok((newlines.len() + 1, l.start - newlines[newlines.len() - 1] + 1))
    }
}

/// A lexeme has a starting position in a string, a length, and a token id. It is a deliberately
/// small data-structure to large input files to be stored efficiently.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Lexeme<TokId: Copy> {
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
        assert_eq!(lexer.set_rule_ids(&map), (None, None));

        let lexemes = lexer.lexer(&"abc 123").lexemes().unwrap();
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
        match lexer.lexer(&"abc").lexemes() {
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
        assert_eq!(lexer.set_rule_ids(&map), (None, None));

        let lexemes = lexer.lexer(&"iff if").lexemes().unwrap();
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

    #[test]
    fn test_line_and_col() {
        let src = "%%
[a-z]+ ID
[ \\n] ;".to_string();
        let mut lexerdef = parse_lex(&src).unwrap();
        let mut map = HashMap::new();
        map.insert("ID", 0);
        assert_eq!(lexerdef.set_rule_ids(&map), (None, None));

        let lexer = lexerdef.lexer("a b c");
        let lexemes = lexer.lexemes().unwrap();
        assert_eq!(lexemes.len(), 3);
        assert_eq!(lexer.line_and_col(&lexemes[1]).unwrap(), (1, 3));

        let lexer = lexerdef.lexer("a b c\n");
        let lexemes = lexer.lexemes().unwrap();
        assert_eq!(lexemes.len(), 3);
        assert_eq!(lexer.line_and_col(&lexemes[1]).unwrap(), (1, 3));

        let lexer = lexerdef.lexer(" a\nb\n  c d");
        let lexemes = lexer.lexemes().unwrap();
        assert_eq!(lexemes.len(), 4);
        assert_eq!(lexer.line_and_col(&lexemes[0]).unwrap(), (1, 2));
        assert_eq!(lexer.line_and_col(&lexemes[1]).unwrap(), (2, 1));
        assert_eq!(lexer.line_and_col(&lexemes[2]).unwrap(), (3, 3));
        assert_eq!(lexer.line_and_col(&lexemes[3]).unwrap(), (3, 5));

        let fake_lexeme = Lexeme{start: 100, len: 1, tok_id: 0};
        if let Ok(_) = lexer.line_and_col(&fake_lexeme) {
            panic!("line_and_col returned Ok(_) when it should have returned Err.");
        }
    }

    #[test]
    fn test_missing_from_lexer_and_parser() {
        let src = "%%
[a-z]+ ID
[ \\n] ;".to_string();
        let mut lexerdef = parse_lex(&src).unwrap();
        let mut map = HashMap::new();
        map.insert("INT", 0);
        let mut missing_from_lexer = HashSet::new();
        missing_from_lexer.insert("INT");
        let mut missing_from_parser = HashSet::new();
        missing_from_parser.insert("ID");
        assert_eq!(lexerdef.set_rule_ids(&map), (Some(missing_from_lexer), Some(missing_from_parser)));

        match lexerdef.lexer(&" a ").lexemes() {
            Ok(_)  => panic!("Invalid input lexed"),
            Err(LexError{idx: 1}) => (),
            Err(e) => panic!("Incorrect error returned {:?}", e)
        };
    }
}
