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

use std::{collections::HashSet, error::Error, fmt};

extern crate regex;
use self::regex::Regex;

type YaccResult<T> = Result<T, YaccParserError>;

use yacc::{
    ast::{GrammarAST, Symbol},
    AssocKind, Precedence, YaccKind
};

/// The various different possible Yacc parser errors.
#[derive(Debug)]
pub enum YaccParserErrorKind {
    IllegalName,
    IllegalString,
    IncompleteRule,
    IncompleteComment,
    IncompleteAction,
    MissingColon,
    PrematureEnd,
    ProgramsNotSupported,
    UnknownDeclaration,
    DuplicatePrecedence,
    PrecNotFollowedByToken,
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

impl Error for YaccParserError {}

impl fmt::Display for YaccParserError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let s = match self.kind {
            YaccParserErrorKind::IllegalName => "Illegal name",
            YaccParserErrorKind::IllegalString => "Illegal string",
            YaccParserErrorKind::IncompleteRule => "Incomplete rule",
            YaccParserErrorKind::IncompleteComment => "Incomplete comment",
            YaccParserErrorKind::IncompleteAction => "Incomplete action",
            YaccParserErrorKind::MissingColon => "Missing colon",
            YaccParserErrorKind::PrematureEnd => "File ends prematurely",
            YaccParserErrorKind::ProgramsNotSupported => "Programs not currently supported",
            YaccParserErrorKind::UnknownDeclaration => "Unknown declaration",
            YaccParserErrorKind::DuplicatePrecedence => "Token already has a precedence",
            YaccParserErrorKind::PrecNotFollowedByToken => "%prec not followed by token name",
            YaccParserErrorKind::DuplicateImplicitTokensDeclaration => {
                "Duplicate %implicit_tokens declaration"
            }
            YaccParserErrorKind::DuplicateStartDeclaration => "Duplicate %start declaration"
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
    static ref RE_NAME: Regex = { Regex::new(r"^[a-zA-Z_.][a-zA-Z0-9_.]*").unwrap() };
    static ref RE_TOKEN: Regex =
        { Regex::new("^(?:(\".+?\")|('.+?')|([a-zA-Z_][a-zA-Z_0-9]*))").unwrap() };
}

/// The actual parser is intended to be entirely opaque from outside users.
impl YaccParser {
    pub(crate) fn new(yacc_kind: YaccKind, src: String) -> YaccParser {
        YaccParser {
            yacc_kind,
            src,
            newlines: vec![0],
            ast: GrammarAST::new()
        }
    }

    pub(crate) fn parse(&mut self) -> YaccResult<usize> {
        // We pass around an index into the *bytes* of self.src. We guarantee that at all times
        // this points to the beginning of a UTF-8 character (since multibyte characters exist, not
        // every byte within the string is also a valid character).
        let mut i = self.parse_declarations(0)?;
        i = self.parse_rules(i)?;
        self.parse_programs(i)
    }

    pub(crate) fn ast(self) -> GrammarAST {
        self.ast
    }

    fn parse_declarations(&mut self, mut i: usize) -> YaccResult<usize> {
        i = self.parse_ws(i)?;
        let mut prec_level = 0;
        while i < self.src.len() {
            if self.lookahead_is("%%", i).is_some() {
                return Ok(i);
            }
            if let Some(j) = self.lookahead_is("%token", i) {
                i = self.parse_ws(j)?;
                while i < self.src.len() {
                    if self.lookahead_is("%", i).is_some() {
                        break;
                    }
                    let (j, n) = self.parse_token(i)?;
                    self.ast.tokens.insert(n);
                    i = self.parse_ws(j)?;
                }
                continue;
            }
            if let Some(j) = self.lookahead_is("%type", i) {
                i = self.parse_ws(j)?;
                while i < self.src.len() {
                    if self.lookahead_is("%", i).is_some() {
                        break;
                    }
                    let (j, n) = self.parse_name(i)?;
                    self.ast.actiontype = Some(n);
                    i = self.parse_ws(j)?;
                }
                continue;
            }
            if let Some(j) = self.lookahead_is("%start", i) {
                if self.ast.start.is_some() {
                    return Err(self.mk_error(YaccParserErrorKind::DuplicateStartDeclaration, i));
                }
                i = self.parse_ws(j)?;
                let (j, n) = self.parse_name(i)?;
                self.ast.start = Some(n);
                i = self.parse_ws(j)?;
                continue;
            }
            if let YaccKind::Eco = self.yacc_kind {
                if let Some(j) = self.lookahead_is("%implicit_tokens", i) {
                    if self.ast.implicit_tokens.is_some() {
                        return Err(self
                            .mk_error(YaccParserErrorKind::DuplicateImplicitTokensDeclaration, i));
                    }
                    let mut implicit_tokens = HashSet::new();
                    i = self.parse_ws(j)?;
                    while j < self.src.len() {
                        if self.lookahead_is("%", i).is_some() {
                            break;
                        }
                        let (j, n) = self.parse_token(i)?;
                        self.ast.tokens.insert(n.clone());
                        implicit_tokens.insert(n);
                        i = self.parse_ws(j)?;
                    }
                    self.ast.implicit_tokens = Some(implicit_tokens);
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

                i = self.parse_ws(k)?;
                while i < self.src.len() {
                    if self.lookahead_is("%", i).is_some() {
                        break;
                    }
                    let (j, n) = self.parse_token(i)?;
                    if self.ast.precs.contains_key(&n) {
                        return Err(self.mk_error(YaccParserErrorKind::DuplicatePrecedence, i));
                    }
                    let prec = Precedence {
                        level: prec_level,
                        kind
                    };
                    self.ast.precs.insert(n, prec);
                    i = self.parse_ws(j)?;
                }
                prec_level += 1;
            }
        }
        Err(self.mk_error(YaccParserErrorKind::PrematureEnd, i - 1))
    }

    fn parse_rules(&mut self, mut i: usize) -> YaccResult<usize> {
        // self.parse_declarations should have left the input at '%%'
        i = self.lookahead_is("%%", i).unwrap();
        i = self.parse_ws(i)?;
        while i < self.src.len() {
            if self.lookahead_is("%%", i).is_some() {
                break;
            }
            i = self.parse_rule(i)?;
            i = self.parse_ws(i)?;
        }
        Ok(i)
    }

    fn parse_rule(&mut self, mut i: usize) -> YaccResult<usize> {
        let (j, rn) = self.parse_name(i)?;
        if self.ast.start.is_none() {
            self.ast.start = Some(rn.clone());
        }
        i = self.parse_ws(j)?;
        match self.lookahead_is(":", i) {
            Some(j) => i = j,
            None => {
                return Err(self.mk_error(YaccParserErrorKind::MissingColon, i));
            }
        }
        let mut syms = Vec::new();
        let mut prec = None;
        let mut action = None;
        i = self.parse_ws(i)?;
        while i < self.src.len() {
            if let Some(j) = self.lookahead_is("|", i) {
                self.ast.add_prod(rn.clone(), syms, prec, action);
                syms = Vec::new();
                prec = None;
                action = None;
                i = self.parse_ws(j)?;
                continue;
            } else if let Some(j) = self.lookahead_is(";", i) {
                self.ast.add_prod(rn.clone(), syms, prec, action);
                return Ok(j);
            }

            if self.lookahead_is("\"", i).is_some() || self.lookahead_is("'", i).is_some() {
                let (j, sym) = self.parse_token(i)?;
                i = self.parse_ws(j)?;
                self.ast.tokens.insert(sym.clone());
                syms.push(Symbol::Token(sym));
            } else if let Some(j) = self.lookahead_is("%prec", i) {
                i = self.parse_ws(j)?;
                let (k, sym) = self.parse_token(i)?;
                if self.ast.tokens.contains(&sym) {
                    prec = Some(sym);
                } else {
                    return Err(self.mk_error(YaccParserErrorKind::PrecNotFollowedByToken, i));
                }
                i = k;
            } else if self.lookahead_is("{", i).is_some() {
                let (j, a) = self.parse_action(i)?;
                i = j;
                action = Some(a);
            } else {
                let (j, sym) = self.parse_token(i)?;
                if self.ast.tokens.contains(&sym) {
                    syms.push(Symbol::Token(sym));
                } else {
                    syms.push(Symbol::Rule(sym));
                }
                i = j;
            }
            i = self.parse_ws(i)?;
        }
        Err(self.mk_error(YaccParserErrorKind::IncompleteRule, i))
    }

    fn parse_name(&self, i: usize) -> YaccResult<(usize, String)> {
        match RE_NAME.find(&self.src[i..]) {
            Some(m) => {
                assert_eq!(m.start(), 0);
                Ok((i + m.end(), self.src[i..i + m.end()].to_string()))
            }
            None => Err(self.mk_error(YaccParserErrorKind::IllegalName, i))
        }
    }

    fn parse_token(&self, i: usize) -> YaccResult<(usize, String)> {
        match RE_TOKEN.find(&self.src[i..]) {
            Some(m) => {
                assert!(m.start() == 0 && m.end() > 0);
                match self.src[i..].chars().next().unwrap() {
                    '"' | '\'' => {
                        assert!('"'.len_utf8() == 1 && '\''.len_utf8() == 1);
                        Ok((i + m.end(), self.src[i + 1..i + m.end() - 1].to_string()))
                    }
                    _ => Ok((i + m.end(), self.src[i..i + m.end()].to_string()))
                }
            }
            None => Err(self.mk_error(YaccParserErrorKind::IllegalString, i))
        }
    }

    fn parse_action(&mut self, i: usize) -> YaccResult<(usize, String)> {
        let mut j = i;
        let mut c = 0; // Count braces
        while j < self.src.len() {
            let ch = self.src[j..].chars().next().unwrap();
            c += match ch {
                '{' => 1,
                '}' if c == 1 => {
                    c = 0;
                    break;
                }
                '}' => -1,
                _ => 0
            };
            j += ch.len_utf8();
        }
        if c > 0 {
            Err(self.mk_error(YaccParserErrorKind::IncompleteAction, j))
        } else {
            let s = self.src[i + 1..j - 1].trim().to_string();
            Ok((j + 1, s))
        }
    }

    fn parse_programs(&mut self, mut i: usize) -> YaccResult<usize> {
        if let Some(j) = self.lookahead_is("%%", i) {
            i = self.parse_ws(j)?;
            if i == self.src.len() {
                Ok(i)
            } else {
                let prog = self.src[i..].to_string();
                i = i + prog.len();
                self.ast.add_programs(prog);
                Ok(i)
            }
        }
        else {
            Ok(i)
        }
    }

    fn parse_ws(&mut self, mut i: usize) -> YaccResult<usize> {
        while i < self.src.len() {
            let c = self.src[i..].chars().nth(0).unwrap();
            match c {
                ' ' | '\t' => i += c.len_utf8(),
                '\n' | '\r' => {
                    self.newlines.push(i + 1);
                    i += c.len_utf8();
                }
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
                                        self.newlines.push(i);
                                        break;
                                    }
                                }
                            }
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
                                    return Err(
                                        self.mk_error(YaccParserErrorKind::IncompleteComment, i)
                                    );
                                }
                            }
                            _ => break
                        }
                    }
                }
                _ => break
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
        YaccParserError { kind: k, line, col }
    }

    fn off_to_line_col(&self, off: usize) -> (usize, usize) {
        if off == self.src.len() {
            let line_off = *self.newlines.iter().last().unwrap();
            return (
                self.newlines.len(),
                self.src[line_off..].chars().count() + 1
            );
        }
        let (line_m1, &line_off) = self
            .newlines
            .iter()
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
    use yacc::{
        ast::{GrammarAST, Production, Symbol},
        AssocKind, Precedence, YaccKind
    };

    fn parse(yacc_kind: YaccKind, s: &str) -> Result<GrammarAST, YaccParserError> {
        let mut yp = YaccParser::new(yacc_kind, s.to_string());
        yp.parse()?;
        Ok(yp.ast())
    }

    fn rule(n: &str) -> Symbol {
        Symbol::Rule(n.to_string())
    }

    fn token(n: &str) -> Symbol {
        Symbol::Token(n.to_string())
    }

    #[test]
    fn test_macro() {
        assert_eq!(Symbol::Token("A".to_string()), token("A"));
    }

    #[test]
    fn test_symbol_eq() {
        assert_eq!(rule("A"), rule("A"));
        assert!(rule("A") != rule("B"));
        assert!(rule("A") != token("A"));
    }

    #[test]
    fn test_rule() {
        let src = "
            %%
            A : 'a';
        ".to_string();
        let grm = parse(YaccKind::Original, &src).unwrap();
        assert_eq!(*grm.get_rule("A").unwrap(), vec![0]);
        assert_eq!(
            grm.prods[grm.get_rule("A").unwrap()[0]],
            Production {
                symbols: vec![token("a")],
                precedence: None,
                action: None
            }
        );
    }

    #[test]
    fn test_rule_production_simple() {
        let src = "
            %%
            A : 'a';
            A : 'b';
        ".to_string();
        let grm = parse(YaccKind::Original, &src).unwrap();
        assert_eq!(
            grm.prods[grm.get_rule("A").unwrap()[0]],
            Production {
                symbols: vec![token("a")],
                precedence: None,
                action: None
            }
        );
        assert_eq!(
            grm.prods[grm.get_rule("A").unwrap()[1]],
            Production {
                symbols: vec![token("b")],
                precedence: None,
                action: None
            }
        );
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

        assert_eq!(
            grm.prods[grm.get_rule("A").unwrap()[0]],
            Production {
                symbols: vec![],
                precedence: None,
                action: None
            }
        );

        assert_eq!(
            grm.prods[grm.get_rule("B").unwrap()[0]],
            Production {
                symbols: vec![token("b")],
                precedence: None,
                action: None
            }
        );
        assert_eq!(
            grm.prods[grm.get_rule("B").unwrap()[1]],
            Production {
                symbols: vec![],
                precedence: None,
                action: None
            }
        );

        assert_eq!(
            grm.prods[grm.get_rule("C").unwrap()[0]],
            Production {
                symbols: vec![],
                precedence: None,
                action: None
            }
        );
        assert_eq!(
            grm.prods[grm.get_rule("C").unwrap()[1]],
            Production {
                symbols: vec![token("c")],
                precedence: None,
                action: None
            }
        );
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
        assert_eq!(
            grm.prods[grm.get_rule("A").unwrap()[0]],
            Production {
                symbols: vec![token("a"), rule("B")],
                precedence: None,
                action: None
            }
        );
    }

    #[test]
    fn test_token_types() {
        let src = "%%\nA : 'a' \"b\";".to_string();
        let grm = parse(YaccKind::Original, &src).unwrap();
        assert_eq!(
            grm.prods[grm.get_rule("A").unwrap()[0]],
            Production {
                symbols: vec![token("a"), token("b")],
                precedence: None,
                action: None
            }
        );
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
        assert_eq!(
            grm.prods[grm.get_rule("A").unwrap()[0]],
            Production {
                symbols: vec![token("T")],
                precedence: None,
                action: None
            }
        );
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
            Ok(_) => panic!("Incorrect token parsed"),
            Err(YaccParserError {
                kind: YaccParserErrorKind::IllegalString,
                line: 1,
                col: 12
            }) => (),
            Err(e) => panic!("Incorrect error returned {}", e)
        }
    }

    #[test]
    fn test_unicode_err2() {
        let src = "%token '❤'\n%%\nA : '❤' | ❤;".to_string();
        match parse(YaccKind::Original, &src) {
            Ok(_) => panic!("Incorrect token parsed"),
            Err(YaccParserError {
                kind: YaccParserErrorKind::IllegalString,
                line: 3,
                col: 11
            }) => (),
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
            Ok(_) => panic!("Incomplete rule parsed"),
            Err(YaccParserError {
                kind: YaccParserErrorKind::IncompleteRule,
                line: 1,
                col: 5
            }) => (),
            Err(e) => panic!("Incorrect error returned {}", e)
        }
    }

    #[test]
    fn test_line_col_report1() {
        let src = "%%
A:".to_string();
        match parse(YaccKind::Original, &src) {
            Ok(_) => panic!("Incomplete rule parsed"),
            Err(YaccParserError {
                kind: YaccParserErrorKind::IncompleteRule,
                line: 2,
                col: 3
            }) => (),
            Err(e) => panic!("Incorrect error returned {}", e)
        }
    }

    #[test]
    fn test_line_col_report2() {
        let src = "%%
A:
".to_string();
        match parse(YaccKind::Original, &src) {
            Ok(_) => panic!("Incomplete rule parsed"),
            Err(YaccParserError {
                kind: YaccParserErrorKind::IncompleteRule,
                line: 3,
                col: 1
            }) => (),
            Err(e) => panic!("Incorrect error returned {}", e)
        }
    }

    #[test]
    fn test_line_col_report3() {
        let src = "

        %woo"
            .to_string();
        match parse(YaccKind::Original, &src) {
            Ok(_) => panic!("Incomplete rule parsed"),
            Err(YaccParserError {
                kind: YaccParserErrorKind::UnknownDeclaration,
                line: 3,
                col: 9
            }) => (),
            Err(e) => panic!("Incorrect error returned {}", e)
        }
    }

    #[test]
    fn test_missing_colon() {
        let src = "%%A x;".to_string();
        match parse(YaccKind::Original, &src) {
            Ok(_) => panic!("Missing colon parsed"),
            Err(YaccParserError {
                kind: YaccParserErrorKind::MissingColon,
                line: 1,
                col: 5
            }) => (),
            Err(e) => panic!("Incorrect error returned {}", e)
        }
    }

    #[test]
    fn test_premature_end() {
        let src = "%token x".to_string();
        match parse(YaccKind::Original, &src) {
            Ok(_) => panic!("Incomplete rule parsed"),
            Err(YaccParserError {
                kind: YaccParserErrorKind::PrematureEnd,
                line: 1,
                col: 8
            }) => (),
            Err(e) => panic!("Incorrect error returned {}", e)
        }
    }

    #[test]
    #[rustfmt::skip]
    fn test_unknown_declaration() {
        let src = "%woo".to_string();
        match parse(YaccKind::Original, &src) {
            Ok(_) => panic!("Unknown declaration parsed"),
            Err(YaccParserError {
                kind: YaccParserErrorKind::UnknownDeclaration,
                line: 1,
                col: 1
            }) => (),
            Err(e) => panic!("Incorrect error returned {}", e)
        }
    }

    #[test]
    #[rustfmt::skip]
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
          ",
        ];
        for src in srcs.iter() {
            match parse(YaccKind::Original, &src.to_string()) {
                Ok(_) => panic!("Duplicate precedence parsed"),
                Err(YaccParserError {
                    kind: YaccParserErrorKind::DuplicatePrecedence,
                    line: 3,
                    ..
                }) => (),
                Err(e) => panic!("Incorrect error returned {}", e)
            }
        }
    }

    #[test]
    #[rustfmt::skip]
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
        match parse(
            YaccKind::Original,
            &"
          %%
          S: 'A' %prec ;
          "
        ) {
            Ok(_) => panic!("Incorrect %prec parsed"),
            Err(YaccParserError {
                kind: YaccParserErrorKind::IllegalString,
                line: 3,
                ..
            }) => (),
            Err(e) => panic!("Incorrect error returned {}", e)
        }

        match parse(
            YaccKind::Original,
            &"
          %%
          S: 'A' %prec B;
          B: ;
          "
        ) {
            Ok(_) => panic!("Incorrect %prec parsed"),
            Err(YaccParserError {
                kind: YaccParserErrorKind::PrecNotFollowedByToken,
                line: 3,
                ..
            }) => (),
            Err(e) => panic!("Incorrect error returned {}", e)
        }
    }

    #[test]
    fn test_no_implicit_tokens_in_original_yacc() {
        match parse(
            YaccKind::Original,
            &"
          %implicit_tokens X
          %%
          "
        ) {
            Ok(_) => panic!(),
            Err(YaccParserError {
                kind: YaccParserErrorKind::UnknownDeclaration,
                line: 2,
                ..
            }) => (),
            Err(e) => panic!("Incorrect error returned {}", e)
        }
    }

    #[test]
    fn test_parse_implicit_tokens() {
        let ast = parse(
            YaccKind::Eco,
            &"
          %implicit_tokens ws1 ws2
          %start R
          %%
          R: 'a';
          "
        ).unwrap();
        assert_eq!(
            ast.implicit_tokens,
            Some(
                ["ws1".to_string(), "ws2".to_string()]
                    .iter()
                    .cloned()
                    .collect()
            )
        );
        assert!(ast.tokens.get("ws1").is_some());
        assert!(ast.tokens.get("ws2").is_some());
    }

    #[test]
    fn test_duplicate_implicit_tokens() {
        match parse(
            YaccKind::Eco,
            &"
          %implicit_tokens X
          %implicit_tokens Y
          %%
          "
        ) {
            Ok(_) => panic!(),
            Err(YaccParserError {
                kind: YaccParserErrorKind::DuplicateImplicitTokensDeclaration,
                line: 3,
                ..
            }) => (),
            Err(e) => panic!("Incorrect error returned {}", e)
        }
    }

    #[test]
    fn test_duplicate_start() {
        match parse(
            YaccKind::Eco,
            &"
          %start X
          %start X
          %%
          "
        ) {
            Ok(_) => panic!(),
            Err(YaccParserError {
                kind: YaccParserErrorKind::DuplicateStartDeclaration,
                line: 3,
                ..
            }) => (),
            Err(e) => panic!("Incorrect error returned {}", e)
        }
    }

    #[test]
    fn test_implicit_start() {
        let ast = parse(
            YaccKind::Eco,
            &"
          %%
          R: ;
          R2: ;
          R3: ;
          "
        ).unwrap();
        assert_eq!(ast.start, Some("R".to_string()));
    }

    #[test]
    fn test_action() {
        let grm = parse(
            YaccKind::Original,
            &"
          %%
          A: 'a' B { println!(\"test\"); }
           ;
          B: 'b' 'c' { add($1, $2); }
           | 'd'
           ;
          "
        ).unwrap();
        assert_eq!(grm.prods[grm.rules["A"][0]].action, Some("println!(\"test\");".to_string()));
        assert_eq!(grm.prods[grm.rules["B"][0]].action, Some("add($1, $2);".to_string()));
        assert_eq!(grm.prods[grm.rules["B"][1]].action, None);
    }

    #[test]
    fn test_programs() {
        let grm = parse(
            YaccKind::Original,
            &"
         %%
         A: 'a';
         %%
         fn foo() {}"
        ).unwrap();
        assert_eq!(grm.programs, Some("fn foo() {}".to_string()));
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

        match parse(
            YaccKind::Original,
            &"
            /* An invalid comment * /
            %token   a
            %%\n
            A : a;"
        ) {
            Ok(_) => panic!(),
            Err(YaccParserError {
                kind: YaccParserErrorKind::IncompleteComment,
                line: 2,
                ..
            }) => (),
            Err(e) => panic!("Incorrect error returned {}", e)
        }

        match parse(
            YaccKind::Original,
            &"
            %token   a
            %%
            /* A valid
             * multi-line comment
             */
            /* An invalid comment * /
            A : a;"
        ) {
            Ok(_) => panic!(),
            Err(YaccParserError {
                kind: YaccParserErrorKind::IncompleteComment,
                line: 7,
                ..
            }) => (),
            Err(e) => panic!("Incorrect error returned {}", e)
        }

        match parse(
            YaccKind::Original,
            &"
            %token   a
            %%
            // Valid comment
            A : a"
        ) {
            Ok(_) => panic!(),
            Err(YaccParserError {
                kind: YaccParserErrorKind::IncompleteRule,
                line: 5,
                ..
            }) => (),
            Err(e) => panic!("Incorrect error returned {}", e)
        }
    }
}
