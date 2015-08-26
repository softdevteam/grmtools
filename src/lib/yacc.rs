use std::fmt;

extern crate regex;
use self::regex::Regex;

type YaccResult<T> = Result<T, YaccError>;

use grammar::{Grammar, Symbol};

pub struct YaccParser {
    src: String,
    grammar: Grammar
}

/// The various different possible Yacc parser errors.
#[derive(Debug)]
pub enum YaccErrorKind {
    IllegalName,
    IllegalString,
    IncompleteRule,
    MissingColon,
    PrematureEnd,
    ProgramsNotSupported,
    UnknownDeclaration
}

/// Any error from the Yacc parser returns an instance of this struct.
#[derive(Debug)]
pub struct YaccError {
    pub kind: YaccErrorKind,
    off:  usize
}

impl fmt::Display for YaccError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let s;
        match self.kind {
            YaccErrorKind::IllegalName          => s = "Illegal name",
            YaccErrorKind::IllegalString        => s = "Illegal string",
            YaccErrorKind::IncompleteRule       => s = "Incomplete rule",
            YaccErrorKind::MissingColon         => s = "Missing colon",
            YaccErrorKind::PrematureEnd         => s = "File ends prematurely",
            YaccErrorKind::ProgramsNotSupported => s = "Programs not currently supported",
            YaccErrorKind::UnknownDeclaration   => s = "Unknown declaration"
        }
        write!(f, "{} at position {}", s, self.off)
    }
}

/// The actual parser is intended to be entirely opaque from outside users.
impl YaccParser {
    fn new(src: String) -> YaccParser {
        YaccParser {
            src: src,
            grammar: Grammar::new()
        }
    }

    fn parse(&mut self) -> YaccResult<usize> {
        let mut i: usize = 0;
        i = try!(self.parse_declarations(i));
        i = try!(self.parse_rules(i));
        // We don't currently support the programs part of a specification. One day we might...
        match self.lookahead_is("%%", i) {
            Some(j) => {
                if try!(self.parse_ws(j)) == self.src.len() { Ok(i) }
                else { Err(YaccError{kind: YaccErrorKind::ProgramsNotSupported, off: i}) }
            }
            None    => Ok(i)
        }
    }

    fn parse_declarations(&mut self, mut i: usize) -> YaccResult<usize> {
        i = try!(self.parse_ws(i));
        while i < self.src.len() {
            if self.lookahead_is("%%", i).is_some() { return Ok(i); }
            if let Some(j) = self.lookahead_is("%token", i) {
                i = try!(self.parse_ws(j));
                while i < self.src.len() {
                    if self.lookahead_is("%", i).is_some() { break; }
                    let (j, n) = try!(self.parse_name(i));
                    self.grammar.tokens.insert(n);
                    i = try!(self.parse_ws(j));
                }
            }
            else if let Some(j) = self.lookahead_is("%start", i) {
                i = try!(self.parse_ws(j));
                let (j, n) = try!(self.parse_name(i));
                self.grammar.start = n;
                i = try!(self.parse_ws(j));
            }
            else {
                return Err(YaccError{kind: YaccErrorKind::UnknownDeclaration, off: i});
            }
        }
        Err(YaccError{kind: YaccErrorKind::PrematureEnd, off: i})
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
        i = try!(self.parse_ws(j));
        match self.lookahead_is(":", i) {
            Some(j) => i = j,
            None    => return Err(YaccError{kind: YaccErrorKind::MissingColon, off: i})
        }
        let mut syms = Vec::new();
        i = try!(self.parse_ws(i));
        while i < self.src.len() {
            if let Some(j) = self.lookahead_is("|", i) {
                self.grammar.add_rule(rn.clone(), syms);
                syms = Vec::new();
                i = try!(self.parse_ws(j));
                continue;
            }
            else if let Some(j) = self.lookahead_is(";", i) {
                self.grammar.add_rule(rn.clone(), syms);
                return Ok(j);
            }

            if self.lookahead_is("\"", i).is_some()
              || self.lookahead_is("'", i).is_some() {
                let (j, sym) = try!(self.parse_terminal(i));
                i = try!(self.parse_ws(j));
                self.grammar.tokens.insert(sym.clone());
                syms.push(Symbol::Terminal(sym));
            }
            else {
                let (j, sym) = try!(self.parse_name(i));
                i = j;
                syms.push(Symbol::Nonterminal(sym));
            }
            i = try!(self.parse_ws(i));
        }
        Err(YaccError{kind: YaccErrorKind::IncompleteRule, off: i})
    }

    fn parse_name(&self, i: usize) -> YaccResult<(usize, String)> {
        let re = Regex::new(r"^[a-zA-Z_.][a-zA-Z0-9_.]*").unwrap();
        match re.find(&self.src[i..]) {
            Some((s, e)) => {
                assert!(s == 0);
                Ok((i + e, self.src[i..i + e].to_string()))
            },
            None         => Err(YaccError{kind: YaccErrorKind::IllegalName, off: i})
        }
    }

    fn parse_terminal(&self, i: usize) -> YaccResult<(usize, String)> {
        let re = Regex::new("^(\".+?\")|('.+?')").unwrap();
        match re.find(&self.src[i..]) {
            Some((s, e)) => {
                assert!(s == 0);
                Ok((i + e, self.src[i + 1..i + e - 1].to_string()))
            },
            None => Err(YaccError{kind: YaccErrorKind::IllegalString, off: i})
        }
    }

    fn parse_ws(&self, i: usize) -> YaccResult<usize> {
        let re = Regex::new(r"^\s+").unwrap();
        match re.find(&self.src[i..]) {
            Some((s, e)) => {
                assert!(s == 0);
                Ok(i + e)
            }
            None => Ok(i)
        }
    }

    fn lookahead_is(&self, s: &'static str, i: usize) -> Option<usize> {
        if i + s.len() <= self.src.len() && &self.src[i..i + s.len()] == s {
            return Some(i + s.len());
        }
        None
    }
}

pub fn parse_yacc(s:&String) -> Result<Grammar, YaccError> {
    let mut yp = YaccParser::new(s.to_string());
    match yp.parse() {
        Ok(_) => Ok(yp.grammar),
        Err(e) => Err(e)
    }
}
