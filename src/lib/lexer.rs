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
use std::collections::HashMap;
use std::convert::TryFrom;
use std::rc::Rc;
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

    /// Return a lexer for the `String` `s` that will lex relative to this `LexerDef`.
    pub fn lexer<'a>(&'a self, s: &'a str) -> Lexer<'a, TokId> {
        Lexer::new(&self, s)
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
                    lxs.push(Lexeme::new(r.tok_id, i, longest));
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
        for (i, n) in self.newlines.borrow().iter().enumerate() {
            if *n > l.start {
                return Ok((i + 1, *n - l.start));
            }
        }
        let newlines_brw = self.newlines.borrow();
        let newlines_len = newlines_brw.len();
        return Ok((newlines_len + 1, l.start - newlines_brw[newlines_len - 1] + 1))
    }
}

/// A lexeme has a starting position in a string, a length, and a token id. It is a deliberately
/// small data-structure to large input files to be stored efficiently.
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
        lexer.set_rule_ids(&map);

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
        let mut lexer = parse_lex(&src).unwrap();
        let mut map = HashMap::new();
        map.insert("ID", 0);
        lexer.set_rule_ids(&map);

        let stream = " a\nb\n  c";
        let lexer = lexer.lexer(&stream);
        let lexemes = lexer.lexemes().unwrap();
        assert_eq!(lexemes.len(), 3);
        assert_eq!(lexer.line_and_col(&lexemes[0]).unwrap(), (1, 2));
        assert_eq!(lexer.line_and_col(&lexemes[1]).unwrap(), (2, 2));
        assert_eq!(lexer.line_and_col(&lexemes[2]).unwrap(), (3, 3));
        let fake_lexeme = Lexeme{start: 100, len: 1, tok_id: 0};
        if let Ok(_) = lexer.line_and_col(&fake_lexeme) {
            panic!("line_and_col returned Ok(_) when it should have returned Err.");
        }
    }
}
