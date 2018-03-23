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

// Note: this is the parser for both YaccKind::Original and YaccKind::Eco yacc kinds.

use std::collections::HashSet;
use std::fmt;

extern crate regex;
use self::regex::Regex;

type YaccResult<T> = Result<T, YaccParserError>;

use yacc::{AssocKind, Precedence, YaccKind};
use yacc::ast::{GrammarAST, Symbol};

/// The various different possible Yacc parser errors.
#[derive(Debug)]
pub enum YaccParserErrorKind {
    IllegalName,
    IllegalString,
    IncompleteRule,
    IncompleteComment,
    MissingColon,
    PrematureEnd,
    ProgramsNotSupported,
    UnknownDeclaration,
    DuplicatePrecedence,
    PrecNotFollowedByTerm,
    DuplicateImplicitTokensDeclaration,
    DuplicateStartDeclaration
}

/// Any error from the Yacc parser returns an instance of this struct.
#[derive(Debug)]
pub struct YaccParserError {
    pub kind: YaccParserErrorKind,
    line: usize,
    col: usize
}

impl fmt::Display for YaccParserError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let s = match self.kind {
            YaccParserErrorKind::IllegalName          => "Illegal name",
            YaccParserErrorKind::IllegalString        => "Illegal string",
            YaccParserErrorKind::IncompleteRule       => "Incomplete rule",
            YaccParserErrorKind::IncompleteComment    => "Incomplete comment",
            YaccParserErrorKind::MissingColon         => "Missing colon",
            YaccParserErrorKind::PrematureEnd         => "File ends prematurely",
            YaccParserErrorKind::ProgramsNotSupported => "Programs not currently supported",
            YaccParserErrorKind::UnknownDeclaration   => "Unknown declaration",
            YaccParserErrorKind::DuplicatePrecedence  => "Token already has a precedence",
            YaccParserErrorKind::PrecNotFollowedByTerm
                                                      => "%prec not followed by token name",
            YaccParserErrorKind::DuplicateImplicitTokensDeclaration
                                                      => "Duplicate %implicit_tokens declaration",
            YaccParserErrorKind::DuplicateStartDeclaration
                                                      => "Duplicate %start declaration",
        };
        write!(f, "{} at line {} column {}", s, self.line, self.col)
    }
}

pub(crate) struct YaccParser {
    yacc_kind: YaccKind,
    src: String,
    newlines: Vec<usize>,
    ast: GrammarAST
}

lazy_static! {
    static ref RE_NAME: Regex = {
        Regex::new(r"^[a-zA-Z_.][a-zA-Z0-9_.]*").unwrap()
    };
    static ref RE_TERMINAL: Regex = {
        Regex::new("^(?:(\".+?\")|('.+?')|([a-zA-Z_][a-zA-Z_0-9]*))").unwrap()
    };
}

/// The actual parser is intended to be entirely opaque from outside users.
impl YaccParser {
    pub (crate) fn new(yacc_kind: YaccKind, src: String) -> YaccParser {
        YaccParser {
            yacc_kind,
            src,
            newlines: vec![0],
            ast : GrammarAST::new()
        }
    }

    pub(crate) fn parse(&mut self) -> YaccResult<usize> {
        // We pass around an index into the *bytes* of self.src. We guarantee that at all times
        // this points to the beginning of a UTF-8 character (since multibyte characters exist, not
        // every byte within the string is also a valid character).
        let mut i = try!(self.parse_declarations(0));
        i = try!(self.parse_rules(i));
        // We don't currently support the programs part of a specification. One day we might...
        match self.lookahead_is("%%", i) {
            Some(j) => {
                if try!(self.parse_ws(j)) == self.src.len() {
                    Ok(i)
                } else {
                    Err(self.mk_error(YaccParserErrorKind::ProgramsNotSupported, i))
                }
            }
            None    => Ok(i)
        }
    }

    pub(crate) fn ast(self) -> GrammarAST {
        self.ast
    }

    fn parse_declarations(&mut self, mut i: usize) -> YaccResult<usize> {
        i = try!(self.parse_ws(i));
        let mut prec_level  = 0;
        while i < self.src.len() {
            if self.lookahead_is("%%", i).is_some() { return Ok(i); }
            if let Some(j) = self.lookahead_is("%token", i) {
                i = try!(self.parse_ws(j));
                while i < self.src.len() {
                    if self.lookahead_is("%", i).is_some() {
                        break;
                    }
                    let (j, n) = try!(self.parse_terminal(i));
                    self.ast.tokens.insert(n);
                    i = try!(self.parse_ws(j));
                }
                continue;
            }
            if let Some(j) = self.lookahead_is("%start", i) {
                if self.ast.start.is_some() {
                    return Err(self.mk_error(YaccParserErrorKind::DuplicateStartDeclaration, i));
                }
                i = try!(self.parse_ws(j));
                let (j, n) = try!(self.parse_name(i));
                self.ast.start = Some(n);
                i = try!(self.parse_ws(j));
                continue;
            }
            if let YaccKind::Eco = self.yacc_kind {
                if let Some(j) = self.lookahead_is("%implicit_tokens", i) {
                    if self.ast.implicit_tokens.is_some() {
                        return Err(self.mk_error(YaccParserErrorKind::DuplicateImplicitTokensDeclaration, i));
                    }
                    let mut implicit_terms = HashSet::new();
                    i = try!(self.parse_ws(j));
                    while j < self.src.len() {
                        if self.lookahead_is("%", i).is_some() {
                            break;
                        }
                        let (j, n) = try!(self.parse_terminal(i));
                        self.ast.tokens.insert(n.clone());
                        implicit_terms.insert(n);
                        i = try!(self.parse_ws(j));
                    }
                    self.ast.implicit_tokens = Some(implicit_terms);
                    continue;
                }
            }
            {
                let k;
                let kind;
                if let Some(j) = self.lookahead_is("%left", i) {
                    kind = AssocKind::Left;
                    k = j;
                } else if let Some(j) = self.lookahead_is("%right", i) {
                    kind = AssocKind::Right;
                    k = j;
                } else if let Some(j) = self.lookahead_is("%nonassoc", i) {
                    kind = AssocKind::Nonassoc;
                    k = j;
                } else {
                    return Err(self.mk_error(YaccParserErrorKind::UnknownDeclaration, i));
                }

                i = try!(self.parse_ws(k));
                while i < self.src.len() {
                    if self.lookahead_is("%", i).is_some() { break; }
                    let (j, n) = try!(self.parse_terminal(i));
                    if self.ast.precs.contains_key(&n) {
                        return Err(self.mk_error(YaccParserErrorKind::DuplicatePrecedence, i));
                    }
                    let prec = Precedence{level: prec_level, kind: kind};
                    self.ast.precs.insert(n, prec);
                    i = try!(self.parse_ws(j));
                }
                prec_level += 1;
            }
        }
        Err(self.mk_error(YaccParserErrorKind::PrematureEnd, i - 1))
    }

    fn parse_rules(&mut self, mut i: usize) -> YaccResult<usize> {
        // self.parse_declarations should have left the input at '%%'
        match self.lookahead_is("%%", i) {
            Some(j) => i = j,
            None    => panic!("Internal error.")
        }
        i = try!(self.parse_ws(i));
        while i < self.src.len() {
            if self.lookahead_is("%%", i).is_some() { break; }
            i = try!(self.parse_rule(i));
            i = try!(self.parse_ws(i));
        }
        Ok(i)
    }

    fn parse_rule(&mut self, mut i: usize) -> YaccResult<usize> {
        let (j, rn) = try!(self.parse_name(i));
        if self.ast.start.is_none() {
            self.ast.start = Some(rn.clone());
        }
        i = try!(self.parse_ws(j));
        match self.lookahead_is(":", i) {
            Some(j) => i = j,
            None    => {
                return Err(self.mk_error(YaccParserErrorKind::MissingColon, i));
            }
        }
        let mut syms = Vec::new();
        let mut prec = None;
        i = try!(self.parse_ws(i));
        while i < self.src.len() {
            if let Some(j) = self.lookahead_is("|", i) {
                self.ast.add_prod(rn.clone(), syms, prec);
                syms = Vec::new();
                prec = None;
                i = try!(self.parse_ws(j));
                continue;
            } else if let Some(j) = self.lookahead_is(";", i) {
                self.ast.add_prod(rn.clone(), syms, prec);
                return Ok(j);
            }

            if self.lookahead_is("\"", i).is_some() || self.lookahead_is("'", i).is_some() {
                let (j, sym) = try!(self.parse_terminal(i));
                i = try!(self.parse_ws(j));
                self.ast.tokens.insert(sym.clone());
                syms.push(Symbol::Term(sym));
            } else if let Some(j) = self.lookahead_is("%prec", i) {
                i = try!(self.parse_ws(j));
                let (k, sym) = try!(self.parse_terminal(i));
                if self.ast.tokens.contains(&sym) {
                    prec = Some(sym);
                } else {
                    return Err(self.mk_error(YaccParserErrorKind::PrecNotFollowedByTerm, i));
                }
                i = k;
            } else {
                let (j, sym) = try!(self.parse_terminal(i));
                if self.ast.tokens.contains(&sym) {
                    syms.push(Symbol::Term(sym));
                } else {
                    syms.push(Symbol::Nonterm(sym));
                }
                i = j;
            }
            i = try!(self.parse_ws(i));
        }
        Err(self.mk_error(YaccParserErrorKind::IncompleteRule, i))
    }

    fn parse_name(&self, i: usize) -> YaccResult<(usize, String)> {
        match RE_NAME.find(&self.src[i..]) {
            Some(m) => {
                assert_eq!(m.start(), 0);
                Ok((i + m.end(), self.src[i..i + m.end()].to_string()))
            },
            None         => {
                Err(self.mk_error(YaccParserErrorKind::IllegalName, i))
            }
        }
    }

    fn parse_terminal(&self, i: usize) -> YaccResult<(usize, String)> {
        match RE_TERMINAL.find(&self.src[i..]) {
            Some(m) => {
                assert!(m.start() == 0 && m.end() > 0);
                match self.src[i..].chars().next().unwrap() {
                    '"' | '\'' => {
                        assert!('"'.len_utf8() == 1 && '\''.len_utf8() == 1);
                        Ok((i + m.end(), self.src[i + 1..i + m.end() - 1].to_string()))
                    },
                    _ =>  Ok((i + m.end(), self.src[i..i + m.end()].to_string()))
                }
            },
            None => {
                Err(self.mk_error(YaccParserErrorKind::IllegalString, i))
            }
        }
    }

    fn parse_ws(&mut self, mut i: usize) -> YaccResult<usize> {
        while i < self.src.len() {
            let c = self.src[i..].chars().nth(0).unwrap();
            match c {
                ' '  | '\t' => i += c.len_utf8(),
                '\n' | '\r' => {
                    self.newlines.push(i + 1);
                    i += c.len_utf8();
                },
                '/' => {
                    if i + c.len_utf8() == self.src.len() {
                        break;
                    } else {
                        let j = i + c.len_utf8();
                        let c = self.src[j..].chars().nth(0).unwrap();
                        match c {
                            '/' => {
                                i = j + c.len_utf8();
                                for c in self.src[i..].chars() {
                                    i += c.len_utf8();
                                    if c == '\n' || c == '\r' {
                                        break;
                                    }
                                }
                            },
                            '*' => {
                                // This is complicated by the fact that we need to deal with
                                // unclosed comments (i.e. '/*' without a corresponding '*/').
                                let mut k = j + c.len_utf8();
                                let mut found = false;
                                while k < self.src.len() {
                                    let c = self.src[k..].chars().nth(0).unwrap();
                                    k += c.len_utf8();
                                    match c {
                                        '\n' | '\r' => self.newlines.push(i + 1),
                                        '*' => (),
                                        _ => continue
                                    }
                                    if k < self.src.len() {
                                        let c = self.src[k..].chars().nth(0).unwrap();
                                        if c == '/' {
                                            i = k + c.len_utf8();
                                            found = true;
                                            break;
                                        }
                                    }
                                }
                                if !found {
                                    return Err(self.mk_error(YaccParserErrorKind::IncompleteComment,
                                                             i));
                                }
                            },
                            _ => break
                        }
                    }
                },
                _  => break
            }
        }
        Ok(i)
    }

    fn lookahead_is(&self, s: &'static str, i: usize) -> Option<usize> {
        if self.src[i..].starts_with(s) {
            Some(i + s.len())
        } else {
            None
        }
    }

    fn mk_error(&self, k: YaccParserErrorKind, off: usize) -> YaccParserError {
        let (line, col) = self.off_to_line_col(off);
        YaccParserError{kind: k, line: line, col: col}
    }

    fn off_to_line_col(&self, off: usize) -> (usize, usize) {
        if off == self.src.len() {
            let line_off = *self.newlines.iter().last().unwrap();
            return (self.newlines.len(), self.src[line_off..].chars().count() + 1);
        }
        let (line_m1, &line_off) = self.newlines.iter()
                                                .enumerate()
                                                .rev()
                                                .find(|&(_, &line_off)| line_off <= off)
                                                .unwrap();
        let c_off = self.src[line_off..]
                        .char_indices()
                        .position(|(c_off, _)| c_off == off - line_off)
                        .unwrap();
        (line_m1 + 1, c_off + 1)
    }
}

#[cfg(test)]
mod test {
    use super::{YaccParser, YaccParserError, YaccParserErrorKind};
    use yacc::{AssocKind, Precedence, YaccKind};
    use yacc::ast::{GrammarAST, Production, Symbol};

    fn parse(yacc_kind: YaccKind, s: &str) -> Result<GrammarAST, YaccParserError> {
        let mut yp = YaccParser::new(yacc_kind, s.to_string());
        try!(yp.parse());
        Ok(yp.ast())
    }

    fn nonterminal(n: &str) -> Symbol {
        Symbol::Nonterm(n.to_string())
    }

    fn terminal(n: &str) -> Symbol {
        Symbol::Term(n.to_string())
    }

    #[test]
    fn test_macro() {
        assert_eq!(Symbol::Term("A".to_string()), terminal("A"));
    }

    #[test]
    fn test_symbol_eq() {
        assert_eq!(nonterminal("A"), nonterminal("A"));
        assert!(nonterminal("A") != nonterminal("B"));
        assert!(nonterminal("A") != terminal("A"));
    }

    #[test]
    fn test_rule() {
        let src = "
            %%
            A : 'a';
        ".to_string();
        let grm = parse(YaccKind::Original, &src).unwrap();
        assert_eq!(*grm.get_rule("A").unwrap(),
                   vec![0]);
        assert_eq!(grm.prods[grm.get_rule("A").unwrap()[0]],
                   Production{symbols: vec![terminal("a")],
                              precedence: None});
    }

    #[test]
    fn test_rule_production_simple() {
        let src = "
            %%
            A : 'a';
            A : 'b';
        ".to_string();
        let grm = parse(YaccKind::Original, &src).unwrap();
        assert_eq!(grm.prods[grm.get_rule("A").unwrap()[0]],
                   Production{symbols: vec![terminal("a")],
                              precedence: None});
        assert_eq!(grm.prods[grm.get_rule("A").unwrap()[1]],
                   Production{symbols: vec![terminal("b")],
                              precedence: None});
    }

    #[test]
    fn test_rule_empty() {
        let src = "
            %%
            A : ;
            B : 'b' | ;
            C : | 'c';
        ".to_string();
        let grm = parse(YaccKind::Original, &src).unwrap();

        assert_eq!(grm.prods[grm.get_rule("A").unwrap()[0]],
                   Production{symbols: vec![],
                              precedence: None});

        assert_eq!(grm.prods[grm.get_rule("B").unwrap()[0]],
                   Production{symbols: vec![terminal("b")],
                              precedence: None});
        assert_eq!(grm.prods[grm.get_rule("B").unwrap()[1]],
                   Production{symbols: vec![],
                              precedence: None});

        assert_eq!(grm.prods[grm.get_rule("C").unwrap()[0]],
                   Production{symbols: vec![],
                              precedence: None});
        assert_eq!(grm.prods[grm.get_rule("C").unwrap()[1]],
                   Production{symbols: vec![terminal("c")],
                              precedence: None});
    }

    #[test]
    fn test_empty_program() {
        let src = "%%\nA : 'a';\n%%".to_string();
        parse(YaccKind::Original, &src).unwrap();
    }

    #[test]
    fn test_multiple_symbols() {
        let src = "%%\nA : 'a' B;".to_string();
        let grm = parse(YaccKind::Original, &src).unwrap();
        assert_eq!(grm.prods[grm.get_rule("A").unwrap()[0]],
                   Production{symbols: vec![terminal("a"), nonterminal("B")],
                              precedence: None});
    }

    #[test]
    fn test_token_types() {
        let src = "%%\nA : 'a' \"b\";".to_string();
        let grm = parse(YaccKind::Original, &src).unwrap();
        assert_eq!(grm.prods[grm.get_rule("A").unwrap()[0]],
                   Production{symbols: vec![terminal("a"), terminal("b")],
                              precedence: None});
    }

    #[test]
    fn test_declaration_start() {
        let src = "%start   A\n%%\nA : a;".to_string();
        let grm = parse(YaccKind::Original, &src).unwrap();
        assert_eq!(grm.start.unwrap(), "A");
    }

    #[test]
    fn test_declaration_token() {
        let src = "%token   a\n%%\nA : a;".to_string();
        let grm = parse(YaccKind::Original, &src).unwrap();
        assert!(grm.has_token("a"));
    }

    #[test]
    fn test_declaration_token_literal() {
        let src = "%token   'a'\n%%\nA : 'a';".to_string();
        let grm = parse(YaccKind::Original, &src).unwrap();
        assert!(grm.has_token("a"));
    }

    #[test]
    fn test_declaration_tokens() {
        let src = "%token   a b c 'd'\n%%\nA : a;".to_string();
        let grm = parse(YaccKind::Original, &src).unwrap();
        assert!(grm.has_token("a"));
        assert!(grm.has_token("b"));
        assert!(grm.has_token("c"));
    }

    #[test]
    fn test_auto_add_tokens() {
        let src = "%%\nA : 'a';".to_string();
        let grm = parse(YaccKind::Original, &src).unwrap();
        assert!(grm.has_token("a"));
    }

    #[test]
    fn test_token_non_literal() {
        let src = "%token T %%\nA : T;".to_string();
        let grm = parse(YaccKind::Original, &src).unwrap();
        assert!(grm.has_token("T"));
        assert_eq!(grm.prods[grm.get_rule("A").unwrap()[0]],
                   Production{symbols: vec![terminal("T")],
                              precedence: None});
    }

    #[test]
    fn test_token_unicode() {
        let src = "%token '❤' %%\nA : '❤';".to_string();
        let grm = parse(YaccKind::Original, &src).unwrap();
        assert!(grm.has_token("❤"));
    }

    #[test]
    fn test_unicode_err1() {
        let src = "%token '❤' ❤;".to_string();
        match parse(YaccKind::Original, &src) {
            Ok(_)  => panic!("Incorrect token parsed"),
            Err(YaccParserError{kind: YaccParserErrorKind::IllegalString, line: 1, col: 12}) => (),
            Err(e) => panic!("Incorrect error returned {}", e)
        }
    }

    #[test]
    fn test_unicode_err2() {
        let src = "%token '❤'\n%%\nA : '❤' | ❤;".to_string();
        match parse(YaccKind::Original, &src) {
            Ok(_)  => panic!("Incorrect token parsed"),
            Err(YaccParserError{kind: YaccParserErrorKind::IllegalString, line: 3, col: 11}) => (),
            Err(e) => panic!("Incorrect error returned {}", e)
        }
    }

    #[test]
    #[should_panic]
    fn test_simple_decl_fail() {
        let src = "%fail x\n%%\nA : a".to_string();
        parse(YaccKind::Original, &src).unwrap();
    }

    #[test]
    #[should_panic]
    fn test_empty() {
        let src = "".to_string();
        parse(YaccKind::Original, &src).unwrap();
    }

    #[test]
    fn test_incomplete_rule1() {
        let src = "%%A:".to_string();
        match parse(YaccKind::Original, &src) {
            Ok(_)  => panic!("Incomplete rule parsed"),
            Err(YaccParserError{kind: YaccParserErrorKind::IncompleteRule, line: 1, col: 5}) => (),
            Err(e) => panic!("Incorrect error returned {}", e)
        }
    }

    #[test]
    fn test_line_col_report1() {
        let src = "%%
A:".to_string();
        match parse(YaccKind::Original, &src) {
            Ok(_)  => panic!("Incomplete rule parsed"),
            Err(YaccParserError{kind: YaccParserErrorKind::IncompleteRule, line: 2, col: 3}) => (),
            Err(e) => panic!("Incorrect error returned {}", e)
        }
    }

    #[test]
    fn test_line_col_report2() {
        let src = "%%
A:
".to_string();
        match parse(YaccKind::Original, &src) {
            Ok(_)  => panic!("Incomplete rule parsed"),
            Err(YaccParserError{kind: YaccParserErrorKind::IncompleteRule, line: 3, col: 1}) => (),
            Err(e) => panic!("Incorrect error returned {}", e)
        }
    }

    #[test]
    fn test_line_col_report3() {
        let src = "

        %woo".to_string();
        match parse(YaccKind::Original, &src) {
            Ok(_)  => panic!("Incomplete rule parsed"),
            Err(YaccParserError{kind: YaccParserErrorKind::UnknownDeclaration, line: 3, col: 9}) => (),
            Err(e) => panic!("Incorrect error returned {}", e)
        }
    }

    #[test]
    fn test_missing_colon() {
        let src = "%%A x;".to_string();
        match parse(YaccKind::Original, &src) {
            Ok(_)  => panic!("Missing colon parsed"),
            Err(YaccParserError{kind: YaccParserErrorKind::MissingColon, line: 1, col: 5}) => (),
            Err(e) => panic!("Incorrect error returned {}", e)
        }
    }

    #[test]
    fn test_premature_end() {
        let src = "%token x".to_string();
        match parse(YaccKind::Original, &src) {
            Ok(_)  => panic!("Incomplete rule parsed"),
            Err(YaccParserError{kind: YaccParserErrorKind::PrematureEnd, line: 1, col: 8}) => (),
            Err(e) => panic!("Incorrect error returned {}", e)
        }
    }

    #[test]
    fn test_programs_not_supported() {
        let src = "%% %%
x".to_string();
        match parse(YaccKind::Original, &src) {
            Ok(_)  => panic!("Programs parsed"),
            Err(YaccParserError{kind: YaccParserErrorKind::ProgramsNotSupported, line: 1, col: 4}) => (),
            Err(e) => panic!("Incorrect error returned {}", e)
        }
    }

    #[test]
    fn test_unknown_declaration() {
        let src = "%woo".to_string();
        match parse(YaccKind::Original, &src) {
            Ok(_)  => panic!("Unknown declaration parsed"),
            Err(YaccParserError{kind: YaccParserErrorKind::UnknownDeclaration, line: 1, col: 1}) => (),
            Err(e) => panic!("Incorrect error returned {}", e)
        }
    }

    #[test]
    fn test_precs() {
        let src = "
          %left '+' '-'
          %left '*'
          %right '/'
          %right '^'
          %nonassoc '~'
          %%
          ".to_string();
        let grm = parse(YaccKind::Original, &src).unwrap();
        assert_eq!(grm.precs.len(), 6);
        assert_eq!(grm.precs["+"], Precedence{level: 0, kind: AssocKind::Left});
        assert_eq!(grm.precs["-"], Precedence{level: 0, kind: AssocKind::Left});
        assert_eq!(grm.precs["*"], Precedence{level: 1, kind: AssocKind::Left});
        assert_eq!(grm.precs["/"], Precedence{level: 2, kind: AssocKind::Right});
        assert_eq!(grm.precs["^"], Precedence{level: 3, kind: AssocKind::Right});
        assert_eq!(grm.precs["~"], Precedence{level: 4, kind: AssocKind::Nonassoc});
    }

    #[test]
    fn test_dup_precs() {
        let srcs = vec![
          "
          %left 'x'
          %left 'x'
          %%
          ",
          "
          %left 'x'
          %right 'x'
          %%
          ",
          "
          %right 'x'
          %right 'x'
          %%
          ",
          "
          %nonassoc 'x'
          %nonassoc 'x'
          %%
          ",
          "
          %left 'x'
          %nonassoc 'x'
          %%
          ",
          "
          %right 'x'
          %nonassoc 'x'
          %%
          "
          ];
        for src in srcs.iter() {
            match parse(YaccKind::Original, &src.to_string()) {
                Ok(_) => panic!("Duplicate precedence parsed"),
                Err(YaccParserError{kind: YaccParserErrorKind::DuplicatePrecedence, line: 3, ..}) => (),
                Err(e) => panic!("Incorrect error returned {}", e)
            }
        }
    }

    #[test]
    fn test_prec_override() {
        // Taken from the Yacc manual
        let src = "
            %left '+' '-'
            %left '*' '/'
            %%
            expr : expr '+' expr
                 | expr '-' expr
                 | expr '*' expr
                 | expr '/' expr
                 | '-'  expr %prec '*'
                 | NAME ;
        ";
        let grm = parse(YaccKind::Original, &src).unwrap();
        assert_eq!(grm.precs.len(), 4);
        assert_eq!(grm.prods[grm.rules["expr"][0]].precedence, None);
        assert_eq!(grm.prods[grm.rules["expr"][3]].symbols.len(), 3);
        assert_eq!(grm.prods[grm.rules["expr"][4]].symbols.len(), 2);
        assert_eq!(grm.prods[grm.rules["expr"][4]].precedence, Some("*".to_string()));
    }

    #[test]
    fn test_bad_prec_overrides() {
        match parse(YaccKind::Original, &"
          %%
          S: 'A' %prec ;
          ") {
                Ok(_) => panic!("Incorrect %prec parsed"),
                Err(YaccParserError{kind: YaccParserErrorKind::IllegalString, line: 3, ..}) => (),
                Err(e) => panic!("Incorrect error returned {}", e)
        }

        match parse(YaccKind::Original, &"
          %%
          S: 'A' %prec B;
          B: ;
          ") {
                Ok(_) => panic!("Incorrect %prec parsed"),
                Err(YaccParserError{kind: YaccParserErrorKind::PrecNotFollowedByTerm, line: 3, ..}) => (),
                Err(e) => panic!("Incorrect error returned {}", e)
        }
    }

    #[test]
    fn test_no_implicit_tokens_in_original_yacc() {
        match parse(YaccKind::Original, &"
          %implicit_tokens X
          %%
          ") {
            Ok(_) => panic!(),
            Err(YaccParserError{kind: YaccParserErrorKind::UnknownDeclaration, line: 2, ..}) => (),
            Err(e) => panic!("Incorrect error returned {}", e)
        }
    }

    #[test]
    fn test_parse_implicit_tokens() {
        let ast = parse(YaccKind::Eco, &"
          %implicit_tokens ws1 ws2
          %start R
          %%
          R: 'a';
          ").unwrap();
        assert_eq!(ast.implicit_tokens, Some(["ws1".to_string(), "ws2".to_string()].iter().cloned().collect()));
        assert!(ast.tokens.get("ws1").is_some());
        assert!(ast.tokens.get("ws2").is_some());
    }

    #[test]
    fn test_duplicate_implicit_tokens() {
        match parse(YaccKind::Eco, &"
          %implicit_tokens X
          %implicit_tokens Y
          %%
          ") {
            Ok(_) => panic!(),
            Err(YaccParserError{kind: YaccParserErrorKind::DuplicateImplicitTokensDeclaration, line: 3, ..}) => (),
            Err(e) => panic!("Incorrect error returned {}", e)
        }
    }

    #[test]
    fn test_duplicate_start() {
        match parse(YaccKind::Eco, &"
          %start X
          %start X
          %%
          ") {
            Ok(_) => panic!(),
            Err(YaccParserError{kind: YaccParserErrorKind::DuplicateStartDeclaration, line: 3, ..}) => (),
            Err(e) => panic!("Incorrect error returned {}", e)
        }
    }

    #[test]
    fn test_implicit_start() {
        let ast = parse(YaccKind::Eco, &"
          %%
          R: ;
          R2: ;
          R3: ;
          ").unwrap();
        assert_eq!(ast.start, Some("R".to_string()));
    }

    #[test]
    fn test_comments() {
        let src = "
            // A valid comment
            %token   a
            /* Another valid comment */
            %%\n
            A : a;";
        let grm = parse(YaccKind::Original, src).unwrap();
        assert!(grm.has_token("a"));

        match parse(YaccKind::Original, &"
            /* An invalid comment * /
            %token   a
            %%\n
            A : a;")
        {
            Ok(_) => panic!(),
            Err(YaccParserError{kind: YaccParserErrorKind::IncompleteComment, line: 2, ..}) => (),
            Err(e) => panic!("Incorrect error returned {}", e)
        }

        match parse(YaccKind::Original, &"
            %token   a
            %%
            /* A valid
             * multi-line comment
             */
            /* An invalid comment * /
            A : a;")
        {
            Ok(_) => panic!(),
            Err(YaccParserError{kind: YaccParserErrorKind::IncompleteComment, line: 7, ..}) => (),
            Err(e) => panic!("Incorrect error returned {}", e)
        }
    }
}
