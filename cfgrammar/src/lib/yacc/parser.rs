// Note: this is the parser for both YaccKind::Original(YaccOriginalActionKind::GenericParseTree) and YaccKind::Eco yacc kinds.

use std::{collections::HashSet, error::Error, fmt};

use lazy_static::lazy_static;
use regex::Regex;

type YaccResult<T> = Result<T, YaccParserError>;

use super::{
    ast::{GrammarAST, Symbol},
    AssocKind, Precedence, YaccKind,
};

/// The various different possible Yacc parser errors.
#[derive(Debug)]
pub enum YaccParserErrorKind {
    IllegalName,
    IllegalString,
    IncompleteRule,
    DuplicateRule,
    IncompleteComment,
    IncompleteAction,
    MissingColon,
    MissingRightArrow,
    MismatchedBrace,
    PrematureEnd,
    ProgramsNotSupported,
    UnknownDeclaration,
    DuplicatePrecedence,
    PrecNotFollowedByToken,
    DuplicateAvoidInsertDeclaration,
    DuplicateImplicitTokensDeclaration,
    DuplicateStartDeclaration,
    DuplicateActiontypeDeclaration,
    DuplicateEPP,
    ReachedEOL,
    InvalidString,
}

/// Any error from the Yacc parser returns an instance of this struct.
#[derive(Debug)]
pub struct YaccParserError {
    pub kind: YaccParserErrorKind,
    line: usize,
    col: usize,
}

impl Error for YaccParserError {}

impl fmt::Display for YaccParserError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let s = match self.kind {
            YaccParserErrorKind::IllegalName => "Illegal name",
            YaccParserErrorKind::IllegalString => "Illegal string",
            YaccParserErrorKind::IncompleteRule => "Incomplete rule",
            YaccParserErrorKind::DuplicateRule => "Duplicate rule",
            YaccParserErrorKind::IncompleteComment => "Incomplete comment",
            YaccParserErrorKind::IncompleteAction => "Incomplete action",
            YaccParserErrorKind::MissingColon => "Missing ':'",
            YaccParserErrorKind::MissingRightArrow => "Missing '->'",
            YaccParserErrorKind::MismatchedBrace => "Mismatched brace",
            YaccParserErrorKind::PrematureEnd => "File ends prematurely",
            YaccParserErrorKind::ProgramsNotSupported => "Programs not currently supported",
            YaccParserErrorKind::UnknownDeclaration => "Unknown declaration",
            YaccParserErrorKind::DuplicatePrecedence => "Token already has a precedence",
            YaccParserErrorKind::PrecNotFollowedByToken => "%prec not followed by token name",
            YaccParserErrorKind::DuplicateAvoidInsertDeclaration => {
                "Duplicate %avoid_insert declaration"
            }
            YaccParserErrorKind::DuplicateImplicitTokensDeclaration => {
                "Duplicate %implicit_tokens declaration"
            }
            YaccParserErrorKind::DuplicateStartDeclaration => "Duplicate %start declaration",
            YaccParserErrorKind::DuplicateActiontypeDeclaration => {
                "Duplicate %actiontype declaration"
            }
            YaccParserErrorKind::DuplicateEPP => "Duplicate %epp declaration for this token",
            YaccParserErrorKind::ReachedEOL => {
                "Reached end of line without finding expected content"
            }
            YaccParserErrorKind::InvalidString => "Invalid string",
        };
        write!(f, "{} at line {} column {}", s, self.line, self.col)
    }
}

pub(crate) struct YaccParser {
    yacc_kind: YaccKind,
    src: String,
    newlines: Vec<usize>,
    ast: GrammarAST,
    global_actiontype: Option<String>,
}

lazy_static! {
    static ref RE_NAME: Regex = Regex::new(r"^[a-zA-Z_.][a-zA-Z0-9_.]*").unwrap();
    static ref RE_TOKEN: Regex =
        Regex::new("^(?:(\".+?\")|('.+?')|([a-zA-Z_][a-zA-Z_0-9]*))").unwrap();
}

/// The actual parser is intended to be entirely opaque from outside users.
impl YaccParser {
    pub(crate) fn new(yacc_kind: YaccKind, src: String) -> YaccParser {
        YaccParser {
            yacc_kind,
            src,
            newlines: vec![0],
            ast: GrammarAST::new(),
            global_actiontype: None,
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
        i = self.parse_ws(i, true)?;
        let mut prec_level = 0;
        while i < self.src.len() {
            if self.lookahead_is("%%", i).is_some() {
                return Ok(i);
            }
            if let Some(j) = self.lookahead_is("%token", i) {
                i = self.parse_ws(j, false)?;
                while i < self.src.len() {
                    if self.lookahead_is("%", i).is_some() {
                        break;
                    }
                    let (j, n) = self.parse_token(i)?;
                    self.ast.tokens.insert(n);
                    i = self.parse_ws(j, true)?;
                }
                continue;
            }
            if let YaccKind::Original(_) = self.yacc_kind {
                if let Some(j) = self.lookahead_is("%actiontype", i) {
                    if self.global_actiontype.is_some() {
                        return Err(
                            self.mk_error(YaccParserErrorKind::DuplicateActiontypeDeclaration, i)
                        );
                    }
                    i = self.parse_ws(j, false)?;
                    let (j, n) = self.parse_to_eol(i)?;
                    self.global_actiontype = Some(n);
                    i = self.parse_ws(j, true)?;
                    continue;
                }
            }
            if let Some(j) = self.lookahead_is("%start", i) {
                if self.ast.start.is_some() {
                    return Err(self.mk_error(YaccParserErrorKind::DuplicateStartDeclaration, i));
                }
                i = self.parse_ws(j, false)?;
                let (j, n) = self.parse_name(i)?;
                self.ast.start = Some(n);
                i = self.parse_ws(j, true)?;
                continue;
            }
            if let Some(j) = self.lookahead_is("%epp", i) {
                i = self.parse_ws(j, false)?;
                let (j, n) = self.parse_token(i)?;
                if self.ast.epp.contains_key(&n) {
                    return Err(self.mk_error(YaccParserErrorKind::DuplicateEPP, i));
                }
                i = self.parse_ws(j, false)?;
                let (j, v) = self.parse_string(i)?;
                self.ast.epp.insert(n, v);
                i = self.parse_ws(j, true)?;
                continue;
            }
            if let Some(j) = self.lookahead_is("%avoid_insert", i) {
                i = self.parse_ws(j, false)?;
                let num_newlines = self.newlines.len();
                if self.ast.avoid_insert.is_none() {
                    self.ast.avoid_insert = Some(HashSet::new());
                }
                while j < self.src.len() && self.newlines.len() == num_newlines {
                    let (j, n) = self.parse_token(i)?;
                    self.ast.tokens.insert(n.clone());
                    if self.ast.avoid_insert.as_ref().unwrap().contains(&n) {
                        return Err(
                            self.mk_error(YaccParserErrorKind::DuplicateAvoidInsertDeclaration, i)
                        );
                    }
                    self.ast.avoid_insert.as_mut().unwrap().insert(n);
                    i = self.parse_ws(j, true)?;
                }
                continue;
            }
            if let Some(j) = self.lookahead_is("%parse_param", i) {
                i = self.parse_param(j)?;
                continue;
            }
            if let YaccKind::Eco = self.yacc_kind {
                if let Some(j) = self.lookahead_is("%implicit_tokens", i) {
                    i = self.parse_ws(j, false)?;
                    let num_newlines = self.newlines.len();
                    if self.ast.implicit_tokens.is_none() {
                        self.ast.implicit_tokens = Some(HashSet::new());
                    }
                    while j < self.src.len() && self.newlines.len() == num_newlines {
                        let (j, n) = self.parse_token(i)?;
                        self.ast.tokens.insert(n.clone());
                        if self.ast.implicit_tokens.as_ref().unwrap().contains(&n) {
                            return Err(self.mk_error(
                                YaccParserErrorKind::DuplicateImplicitTokensDeclaration,
                                i,
                            ));
                        }
                        self.ast.implicit_tokens.as_mut().unwrap().insert(n);
                        i = self.parse_ws(j, true)?;
                    }
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

                i = self.parse_ws(k, false)?;
                let num_newlines = self.newlines.len();
                while i < self.src.len() && num_newlines == self.newlines.len() {
                    let (j, n) = self.parse_token(i)?;
                    if self.ast.precs.contains_key(&n) {
                        return Err(self.mk_error(YaccParserErrorKind::DuplicatePrecedence, i));
                    }
                    let prec = Precedence {
                        level: prec_level,
                        kind,
                    };
                    self.ast.precs.insert(n, prec);
                    i = self.parse_ws(j, true)?;
                }
                prec_level += 1;
            }
        }
        Err(self.mk_error(YaccParserErrorKind::PrematureEnd, i - 1))
    }

    fn parse_rules(&mut self, mut i: usize) -> YaccResult<usize> {
        // self.parse_declarations should have left the input at '%%'
        i = self.lookahead_is("%%", i).unwrap();
        i = self.parse_ws(i, true)?;
        while i < self.src.len() {
            if self.lookahead_is("%%", i).is_some() {
                break;
            }
            i = self.parse_rule(i)?;
            i = self.parse_ws(i, true)?;
        }
        Ok(i)
    }

    fn parse_rule(&mut self, mut i: usize) -> YaccResult<usize> {
        let (j, rn) = self.parse_name(i)?;
        if self.ast.start.is_none() {
            self.ast.start = Some(rn.clone());
        }
        match self.yacc_kind {
            YaccKind::Original(_) | YaccKind::Eco => {
                if self.ast.get_rule(&rn).is_none() {
                    self.ast
                        .add_rule(rn.clone(), self.global_actiontype.clone());
                }
                i = j;
            }
            YaccKind::Grmtools => {
                if self.ast.get_rule(&rn).is_some() {
                    return Err(self.mk_error(YaccParserErrorKind::DuplicateRule, i));
                }
                i = self.parse_ws(j, true)?;
                if let Some(j) = self.lookahead_is("->", i) {
                    i = j;
                } else {
                    return Err(self.mk_error(YaccParserErrorKind::MissingRightArrow, i));
                }
                i = self.parse_ws(i, true)?;
                let (j, actiont) = self.parse_to_single_colon(i)?;
                self.ast.add_rule(rn.clone(), Some(actiont));
                i = j;
            }
        }
        i = self.parse_ws(i, true)?;
        match self.lookahead_is(":", i) {
            Some(j) => i = j,
            None => {
                return Err(self.mk_error(YaccParserErrorKind::MissingColon, i));
            }
        }
        let mut syms = Vec::new();
        let mut prec = None;
        let mut action = None;
        i = self.parse_ws(i, true)?;
        while i < self.src.len() {
            if let Some(j) = self.lookahead_is("|", i) {
                self.ast.add_prod(rn.clone(), syms, prec, action);
                syms = Vec::new();
                prec = None;
                action = None;
                i = self.parse_ws(j, true)?;
                continue;
            } else if let Some(j) = self.lookahead_is(";", i) {
                self.ast.add_prod(rn, syms, prec, action);
                return Ok(j);
            }

            if self.lookahead_is("\"", i).is_some() || self.lookahead_is("'", i).is_some() {
                let (j, sym) = self.parse_token(i)?;
                i = self.parse_ws(j, true)?;
                self.ast.tokens.insert(sym.clone());
                syms.push(Symbol::Token(sym));
            } else if let Some(j) = self.lookahead_is("%prec", i) {
                i = self.parse_ws(j, true)?;
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
            i = self.parse_ws(i, true)?;
        }
        Err(self.mk_error(YaccParserErrorKind::IncompleteRule, i))
    }

    fn parse_name(&self, i: usize) -> YaccResult<(usize, String)> {
        match RE_NAME.find(&self.src[i..]) {
            Some(m) => {
                assert_eq!(m.start(), 0);
                Ok((i + m.end(), self.src[i..i + m.end()].to_string()))
            }
            None => Err(self.mk_error(YaccParserErrorKind::IllegalName, i)),
        }
    }

    fn parse_token(&self, i: usize) -> YaccResult<(usize, String)> {
        match RE_TOKEN.find(&self.src[i..]) {
            Some(m) => {
                assert!(m.start() == 0 && m.end() > 0);
                match self.src[i..].chars().next().unwrap() {
                    '"' | '\'' => {
                        debug_assert!('"'.len_utf8() == 1 && '\''.len_utf8() == 1);
                        Ok((i + m.end(), self.src[i + 1..i + m.end() - 1].to_string()))
                    }
                    _ => Ok((i + m.end(), self.src[i..i + m.end()].to_string())),
                }
            }
            None => Err(self.mk_error(YaccParserErrorKind::IllegalString, i)),
        }
    }

    fn parse_action(&mut self, i: usize) -> YaccResult<(usize, String)> {
        let mut j = i;
        let mut c = 0; // Count braces
        while j < self.src.len() {
            let ch = self.src[j..].chars().next().unwrap();
            match ch {
                '{' => c += 1,
                '}' if c == 1 => {
                    c = 0;
                    break;
                }
                '}' => c -= 1,
                '\n' | '\r' => {
                    self.newlines.push(j + 1);
                }
                _ => (),
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
            i = self.parse_ws(j, true)?;
            if i == self.src.len() {
                Ok(i)
            } else {
                let prog = self.src[i..].to_string();
                i += prog.len();
                self.ast.add_programs(prog);
                Ok(i)
            }
        } else {
            Ok(i)
        }
    }

    // Handle parse_param declarations of the form:
    // %parse_param <'a>(x: u32, y : (u32, u32))
    fn parse_param(&mut self, mut i: usize) -> YaccResult<usize> {
        i = self.parse_ws(i, false)?;
        // First gobble up all of the '<' lifetime ',' ... '>
        if let Some(mut j) = self.lookahead_is("<", i) {
            let mut k = j;
            let mut lifetimes = HashSet::new();
            let mut add_lifetime = |j, k, c: char| {
                let s = self.src[j..k].trim().to_string();
                lifetimes.insert(s);
                k + c.len_utf8()
            };

            while k < self.src.len() {
                let c = self.src[k..].chars().next().unwrap();
                match c {
                    '\n' | '\r' => return Err(self.mk_error(YaccParserErrorKind::ReachedEOL, k)),
                    ',' => {
                        k = add_lifetime(j, k, ',');
                        j = k;
                    }
                    '>' => {
                        k = add_lifetime(j, k, '>');
                        break;
                    }
                    _ => k += c.len_utf8(),
                }
            }
            self.ast.parse_param_lifetimes = Some(lifetimes);
            i = k;
        }

        // Next, the '(' pattern : type, ... ')'
        i = self.parse_ws(i, false)?;
        if self.lookahead_is("(", i).is_some() {
            let mut j = i;
            let mut bindings: Vec<(String, String)> = Vec::new();
            while j < self.src.len() && self.lookahead_is(")", j).is_none() {
                let c = self.src[j..].chars().next().unwrap();
                j += c.len_utf8();

                // Some binding name, or pattern.
                j = self.parse_ws(j, false)?;
                let (k, binding) = self.parse_to_single_colon(j)?;
                let (k, typ) = self.parse_param_rust_type(k + ':'.len_utf8())?;
                j = k;
                bindings.push((binding.trim_end().to_string(), typ));
            }
            if !bindings.is_empty() {
                self.ast.parse_param_bindings = Some(bindings);
            }
            i = j;
        }
        let (i, _) = self.parse_to_eol(i)?;
        Ok(self.parse_ws(i, true)?)
    }

    // Parse a rust type, followed by either a ',' character or an unbalanced ')'
    // Return the char indice of the trailing character,
    fn parse_param_rust_type(&mut self, i: usize) -> YaccResult<(usize, String)> {
        let i = self.parse_ws(i, false)?;
        let mut j = i;
        let mut brace_count = 0;

        while j < self.src.len() {
            let c = self.src[j..].chars().next().unwrap();
            match c {
                '\n' | '\r' => return Err(self.mk_error(YaccParserErrorKind::ReachedEOL, j)),
                ')' | ',' if brace_count == 0 => {
                    return Ok((j, self.src[i..j].trim_end().to_string()));
                }
                '(' | '{' | '[' | '<' => {
                    brace_count += 1;
                    j += c.len_utf8();
                }
                ')' | '}' | '>' | ']' => {
                    if brace_count == 0 {
                        return Err(self.mk_error(YaccParserErrorKind::MismatchedBrace, j));
                    }
                    brace_count -= 1;
                    j += c.len_utf8();
                }
                c => j += c.len_utf8(),
            }
        }
        Err(self.mk_error(YaccParserErrorKind::PrematureEnd, j))
    }

    /// Parse up to (but do not include) the end of line (or, if it comes sooner, the end of file).
    fn parse_to_eol(&mut self, i: usize) -> YaccResult<(usize, String)> {
        let mut j = i;
        while j < self.src.len() {
            let c = self.src[j..].chars().next().unwrap();
            match c {
                '\n' | '\r' => break,
                _ => j += c.len_utf8(),
            }
        }
        Ok((j, self.src[i..j].to_string()))
    }

    /// Parse up to (but do not include) a single colon (double colons are allowed so that strings
    /// like `a::b::c:` treat `a::b::c` as a single name. Errors if EOL encountered.
    fn parse_to_single_colon(&mut self, i: usize) -> YaccResult<(usize, String)> {
        let mut j = i;
        while j < self.src.len() {
            let c = self.src[j..].chars().next().unwrap();
            match c {
                ':' => {
                    let k = j + ':'.len_utf8();
                    if k == self.src.len() || !self.src[k..].starts_with(':') {
                        return Ok((j, self.src[i..j].to_string()));
                    }
                    j += 2 * ':'.len_utf8();
                }
                '\n' | '\r' => {
                    self.newlines.push(i + 1);
                    j += c.len_utf8();
                }
                _ => j += c.len_utf8(),
            }
        }
        Err(self.mk_error(YaccParserErrorKind::ReachedEOL, j))
    }

    /// Parse a quoted string, allowing escape characters.
    fn parse_string(&mut self, mut i: usize) -> YaccResult<(usize, String)> {
        let qc = if self.lookahead_is("'", i).is_some() {
            '\''
        } else if self.lookahead_is("\"", i).is_some() {
            '"'
        } else {
            return Err(self.mk_error(YaccParserErrorKind::InvalidString, i));
        };

        debug_assert!('"'.len_utf8() == 1 && '\''.len_utf8() == 1);
        // Because we can encounter escape characters, we can't simply match text and slurp it into
        // a String in one go (otherwise we'd include the escape characters). Conceptually we have
        // to build the String up byte by byte, skipping escape characters, but that's slow.
        // Instead we append chunks of the string up to (but excluding) escape characters.
        let mut s = String::new();
        i += 1;
        let mut j = i;
        while j < self.src.len() {
            let c = self.src[j..].chars().next().unwrap();
            match c {
                '\n' | '\r' => {
                    return Err(self.mk_error(YaccParserErrorKind::InvalidString, j));
                }
                x if x == qc => {
                    s.push_str(&self.src[i..j]);
                    return Ok((j + 1, s));
                }
                '\\' => {
                    debug_assert!('\\'.len_utf8() == 1);
                    match self.src[j + 1..].chars().next().unwrap() {
                        '\'' | '"' => {
                            s.push_str(&self.src[i..j]);
                            i = j + 1;
                            j += 2;
                        }
                        _ => {
                            return Err(self.mk_error(YaccParserErrorKind::InvalidString, j));
                        }
                    }
                }
                _ => j += c.len_utf8(),
            }
        }
        Err(self.mk_error(YaccParserErrorKind::InvalidString, j))
    }

    /// Skip whitespace from `i` onwards. If `inc_newlines` is `false`, will return `Err` if a
    /// newline is encountered; otherwise newlines are consumed and skipped.
    fn parse_ws(&mut self, mut i: usize, inc_newlines: bool) -> YaccResult<usize> {
        while i < self.src.len() {
            let c = self.src[i..].chars().next().unwrap();
            match c {
                ' ' | '\t' => i += c.len_utf8(),
                '\n' | '\r' => {
                    if !inc_newlines {
                        return Err(self.mk_error(YaccParserErrorKind::ReachedEOL, i));
                    }
                    self.newlines.push(i + 1);
                    i += c.len_utf8();
                }
                '/' => {
                    if i + c.len_utf8() == self.src.len() {
                        break;
                    } else {
                        let j = i + c.len_utf8();
                        let c = self.src[j..].chars().next().unwrap();
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
                                    let c = self.src[k..].chars().next().unwrap();
                                    k += c.len_utf8();
                                    match c {
                                        '\n' | '\r' => {
                                            if !inc_newlines {
                                                return Err(self
                                                    .mk_error(YaccParserErrorKind::ReachedEOL, i));
                                            }
                                            self.newlines.push(i + 1);
                                        }
                                        '*' => (),
                                        _ => continue,
                                    }
                                    if k < self.src.len() {
                                        let c = self.src[k..].chars().next().unwrap();
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
                            _ => break,
                        }
                    }
                }
                _ => break,
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
                self.src[line_off..].chars().count() + 1,
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
    use std::{collections::HashSet, iter::FromIterator};

    use super::{
        super::{
            ast::{GrammarAST, Production, Symbol},
            AssocKind, Precedence, YaccKind, YaccOriginalActionKind,
        },
        YaccParser, YaccParserError, YaccParserErrorKind,
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
        "
        .to_string();
        let grm = parse(
            YaccKind::Original(YaccOriginalActionKind::GenericParseTree),
            &src,
        )
        .unwrap();
        assert_eq!(grm.get_rule("A").unwrap().pidxs, vec![0]);
        assert_eq!(
            grm.prods[grm.get_rule("A").unwrap().pidxs[0]],
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
        "
        .to_string();
        let grm = parse(
            YaccKind::Original(YaccOriginalActionKind::GenericParseTree),
            &src,
        )
        .unwrap();
        assert_eq!(
            grm.prods[grm.get_rule("A").unwrap().pidxs[0]],
            Production {
                symbols: vec![token("a")],
                precedence: None,
                action: None
            }
        );
        assert_eq!(
            grm.prods[grm.get_rule("A").unwrap().pidxs[1]],
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
        "
        .to_string();
        let grm = parse(
            YaccKind::Original(YaccOriginalActionKind::GenericParseTree),
            &src,
        )
        .unwrap();

        assert_eq!(
            grm.prods[grm.get_rule("A").unwrap().pidxs[0]],
            Production {
                symbols: vec![],
                precedence: None,
                action: None
            }
        );

        assert_eq!(
            grm.prods[grm.get_rule("B").unwrap().pidxs[0]],
            Production {
                symbols: vec![token("b")],
                precedence: None,
                action: None
            }
        );
        assert_eq!(
            grm.prods[grm.get_rule("B").unwrap().pidxs[1]],
            Production {
                symbols: vec![],
                precedence: None,
                action: None
            }
        );

        assert_eq!(
            grm.prods[grm.get_rule("C").unwrap().pidxs[0]],
            Production {
                symbols: vec![],
                precedence: None,
                action: None
            }
        );
        assert_eq!(
            grm.prods[grm.get_rule("C").unwrap().pidxs[1]],
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
        parse(
            YaccKind::Original(YaccOriginalActionKind::GenericParseTree),
            &src,
        )
        .unwrap();
    }

    #[test]
    fn test_multiple_symbols() {
        let src = "%%\nA : 'a' B;".to_string();
        let grm = parse(
            YaccKind::Original(YaccOriginalActionKind::GenericParseTree),
            &src,
        )
        .unwrap();
        assert_eq!(
            grm.prods[grm.get_rule("A").unwrap().pidxs[0]],
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
        let grm = parse(
            YaccKind::Original(YaccOriginalActionKind::GenericParseTree),
            &src,
        )
        .unwrap();
        assert_eq!(
            grm.prods[grm.get_rule("A").unwrap().pidxs[0]],
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
        let grm = parse(
            YaccKind::Original(YaccOriginalActionKind::GenericParseTree),
            &src,
        )
        .unwrap();
        assert_eq!(grm.start.unwrap(), "A");
    }

    #[test]
    fn test_declaration_token() {
        let src = "%token   a\n%%\nA : a;".to_string();
        let grm = parse(
            YaccKind::Original(YaccOriginalActionKind::GenericParseTree),
            &src,
        )
        .unwrap();
        assert!(grm.has_token("a"));
    }

    #[test]
    fn test_declaration_token_literal() {
        let src = "%token   'a'\n%%\nA : 'a';".to_string();
        let grm = parse(
            YaccKind::Original(YaccOriginalActionKind::GenericParseTree),
            &src,
        )
        .unwrap();
        assert!(grm.has_token("a"));
    }

    #[test]
    fn test_declaration_tokens() {
        let src = "%token   a b c 'd'\n%%\nA : a;".to_string();
        let grm = parse(
            YaccKind::Original(YaccOriginalActionKind::GenericParseTree),
            &src,
        )
        .unwrap();
        assert!(grm.has_token("a"));
        assert!(grm.has_token("b"));
        assert!(grm.has_token("c"));
    }

    #[test]
    fn test_auto_add_tokens() {
        let src = "%%\nA : 'a';".to_string();
        let grm = parse(
            YaccKind::Original(YaccOriginalActionKind::GenericParseTree),
            &src,
        )
        .unwrap();
        assert!(grm.has_token("a"));
    }

    #[test]
    fn test_token_non_literal() {
        let src = "%token T %%\nA : T;".to_string();
        let grm = parse(
            YaccKind::Original(YaccOriginalActionKind::GenericParseTree),
            &src,
        )
        .unwrap();
        assert!(grm.has_token("T"));
        assert_eq!(
            grm.prods[grm.get_rule("A").unwrap().pidxs[0]],
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
        let grm = parse(
            YaccKind::Original(YaccOriginalActionKind::GenericParseTree),
            &src,
        )
        .unwrap();
        assert!(grm.has_token("❤"));
    }

    #[test]
    fn test_unicode_err1() {
        let src = "%token '❤' ❤;".to_string();
        match parse(
            YaccKind::Original(YaccOriginalActionKind::GenericParseTree),
            &src,
        ) {
            Ok(_) => panic!("Incorrect token parsed"),
            Err(YaccParserError {
                kind: YaccParserErrorKind::IllegalString,
                line: 1,
                col: 12,
            }) => (),
            Err(e) => panic!("Incorrect error returned {}", e),
        }
    }

    #[test]
    fn test_unicode_err2() {
        let src = "%token '❤'\n%%\nA : '❤' | ❤;".to_string();
        match parse(
            YaccKind::Original(YaccOriginalActionKind::GenericParseTree),
            &src,
        ) {
            Ok(_) => panic!("Incorrect token parsed"),
            Err(YaccParserError {
                kind: YaccParserErrorKind::IllegalString,
                line: 3,
                col: 11,
            }) => (),
            Err(e) => panic!("Incorrect error returned {}", e),
        }
    }

    #[test]
    #[should_panic]
    fn test_simple_decl_fail() {
        let src = "%fail x\n%%\nA : a".to_string();
        parse(
            YaccKind::Original(YaccOriginalActionKind::GenericParseTree),
            &src,
        )
        .unwrap();
    }

    #[test]
    #[should_panic]
    fn test_empty() {
        let src = "".to_string();
        parse(
            YaccKind::Original(YaccOriginalActionKind::GenericParseTree),
            &src,
        )
        .unwrap();
    }

    #[test]
    fn test_incomplete_rule1() {
        let src = "%%A:".to_string();
        match parse(
            YaccKind::Original(YaccOriginalActionKind::GenericParseTree),
            &src,
        ) {
            Ok(_) => panic!("Incomplete rule parsed"),
            Err(YaccParserError {
                kind: YaccParserErrorKind::IncompleteRule,
                line: 1,
                col: 5,
            }) => (),
            Err(e) => panic!("Incorrect error returned {}", e),
        }
    }

    #[test]
    fn test_line_col_report1() {
        let src = "%%
A:"
        .to_string();
        match parse(
            YaccKind::Original(YaccOriginalActionKind::GenericParseTree),
            &src,
        ) {
            Ok(_) => panic!("Incomplete rule parsed"),
            Err(YaccParserError {
                kind: YaccParserErrorKind::IncompleteRule,
                line: 2,
                col: 3,
            }) => (),
            Err(e) => panic!("Incorrect error returned {}", e),
        }
    }

    #[test]
    fn test_line_col_report2() {
        let src = "%%
A:
"
        .to_string();
        match parse(
            YaccKind::Original(YaccOriginalActionKind::GenericParseTree),
            &src,
        ) {
            Ok(_) => panic!("Incomplete rule parsed"),
            Err(YaccParserError {
                kind: YaccParserErrorKind::IncompleteRule,
                line: 3,
                col: 1,
            }) => (),
            Err(e) => panic!("Incorrect error returned {}", e),
        }
    }

    #[test]
    fn test_line_col_report3() {
        let src = "

        %woo"
            .to_string();
        match parse(
            YaccKind::Original(YaccOriginalActionKind::GenericParseTree),
            &src,
        ) {
            Ok(_) => panic!("Incomplete rule parsed"),
            Err(YaccParserError {
                kind: YaccParserErrorKind::UnknownDeclaration,
                line: 3,
                col: 9,
            }) => (),
            Err(e) => panic!("Incorrect error returned {}", e),
        }
    }

    #[test]
    fn test_missing_colon() {
        let src = "%%A x;".to_string();
        match parse(
            YaccKind::Original(YaccOriginalActionKind::GenericParseTree),
            &src,
        ) {
            Ok(_) => panic!("Missing colon parsed"),
            Err(YaccParserError {
                kind: YaccParserErrorKind::MissingColon,
                line: 1,
                col: 5,
            }) => (),
            Err(e) => panic!("Incorrect error returned {}", e),
        }
    }

    #[test]
    fn test_premature_end() {
        let src = "%token x".to_string();
        match parse(
            YaccKind::Original(YaccOriginalActionKind::GenericParseTree),
            &src,
        ) {
            Ok(_) => panic!("Incomplete rule parsed"),
            Err(YaccParserError {
                kind: YaccParserErrorKind::PrematureEnd,
                line: 1,
                col: 8,
            }) => (),
            Err(e) => panic!("Incorrect error returned {}", e),
        }
    }

    #[test]
    fn test_same_line() {
        let src = "%token
x"
        .to_string();
        match parse(
            YaccKind::Original(YaccOriginalActionKind::GenericParseTree),
            &src,
        ) {
            Ok(_) => panic!("Incomplete rule parsed"),
            Err(YaccParserError {
                kind: YaccParserErrorKind::ReachedEOL,
                line: 1,
                col: 7,
            }) => (),
            Err(e) => panic!("Incorrect error returned {}", e),
        }
    }

    #[test]
    #[rustfmt::skip]
    fn test_unknown_declaration() {
        let src = "%woo".to_string();
        match parse(YaccKind::Original(YaccOriginalActionKind::GenericParseTree), &src) {
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
    fn test_grmtools_format() {
        let src = "
          %start A
          %%
          A -> T: 'b';
          B -> Result<(), T>: 'c';
          C -> ::std::result::Result<(), T>: 'd';
          "
        .to_string();
        let grm = parse(YaccKind::Grmtools, &src).unwrap();
        assert_eq!(grm.rules["A"].actiont, Some("T".to_string()));
        assert_eq!(grm.rules["B"].actiont, Some("Result<(), T>".to_string()));
        assert_eq!(
            grm.rules["C"].actiont,
            Some("::std::result::Result<(), T>".to_string())
        );
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
        let grm = parse(YaccKind::Original(YaccOriginalActionKind::GenericParseTree), &src).unwrap();
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
            match parse(
                YaccKind::Original(YaccOriginalActionKind::GenericParseTree),
                &src.to_string(),
            ) {
                Ok(_) => panic!("Duplicate precedence parsed"),
                Err(YaccParserError {
                    kind: YaccParserErrorKind::DuplicatePrecedence,
                    line: 3,
                    ..
                }) => (),
                Err(e) => panic!("Incorrect error returned {}", e),
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
        let grm = parse(YaccKind::Original(YaccOriginalActionKind::GenericParseTree), &src).unwrap();
        assert_eq!(grm.precs.len(), 4);
        assert_eq!(grm.prods[grm.rules["expr"].pidxs[0]].precedence, None);
        assert_eq!(grm.prods[grm.rules["expr"].pidxs[3]].symbols.len(), 3);
        assert_eq!(grm.prods[grm.rules["expr"].pidxs[4]].symbols.len(), 2);
        assert_eq!(grm.prods[grm.rules["expr"].pidxs[4]].precedence, Some("*".to_string()));
    }

    #[test]
    fn test_bad_prec_overrides() {
        match parse(
            YaccKind::Original(YaccOriginalActionKind::GenericParseTree),
            &"
          %%
          S: 'A' %prec ;
          ",
        ) {
            Ok(_) => panic!("Incorrect %prec parsed"),
            Err(YaccParserError {
                kind: YaccParserErrorKind::IllegalString,
                line: 3,
                ..
            }) => (),
            Err(e) => panic!("Incorrect error returned {}", e),
        }

        match parse(
            YaccKind::Original(YaccOriginalActionKind::GenericParseTree),
            &"
          %%
          S: 'A' %prec B;
          B: ;
          ",
        ) {
            Ok(_) => panic!("Incorrect %prec parsed"),
            Err(YaccParserError {
                kind: YaccParserErrorKind::PrecNotFollowedByToken,
                line: 3,
                ..
            }) => (),
            Err(e) => panic!("Incorrect error returned {}", e),
        }
    }

    #[test]
    fn test_parse_avoid_insert() {
        let ast = parse(
            YaccKind::Eco,
            &"
          %avoid_insert ws1 ws2
          %start R
          %%
          R: 'a';
          ",
        )
        .unwrap();
        assert_eq!(
            ast.avoid_insert,
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
    fn test_multiple_avoid_insert() {
        let ast = parse(
            YaccKind::Eco,
            &"
          %avoid_insert X
          %avoid_insert Y
          %%
          ",
        )
        .unwrap();
        assert_eq!(
            ast.avoid_insert,
            Some(["X".to_string(), "Y".to_string()].iter().cloned().collect())
        );
    }

    #[test]
    fn test_duplicate_avoid_insert() {
        match parse(
            YaccKind::Eco,
            &"
          %avoid_insert X Y
          %avoid_insert Y
          %%
          ",
        ) {
            Ok(_) => panic!(),
            Err(YaccParserError {
                kind: YaccParserErrorKind::DuplicateAvoidInsertDeclaration,
                line: 3,
                ..
            }) => (),
            Err(e) => panic!("Incorrect error returned {}", e),
        }
    }

    #[test]
    fn test_duplicate_avoid_insert2() {
        match parse(
            YaccKind::Eco,
            &"
          %avoid_insert X
          %avoid_insert Y Y
          %%
          ",
        ) {
            Ok(_) => panic!(),
            Err(YaccParserError {
                kind: YaccParserErrorKind::DuplicateAvoidInsertDeclaration,
                line: 3,
                ..
            }) => (),
            Err(e) => panic!("Incorrect error returned {}", e),
        }
    }

    #[test]
    fn test_no_implicit_tokens_in_original_yacc() {
        match parse(
            YaccKind::Original(YaccOriginalActionKind::GenericParseTree),
            &"
          %implicit_tokens X
          %%
          ",
        ) {
            Ok(_) => panic!(),
            Err(YaccParserError {
                kind: YaccParserErrorKind::UnknownDeclaration,
                line: 2,
                ..
            }) => (),
            Err(e) => panic!("Incorrect error returned {}", e),
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
          ",
        )
        .unwrap();
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
    fn test_multiple_implicit_tokens() {
        let ast = parse(
            YaccKind::Eco,
            &"
          %implicit_tokens X
          %implicit_tokens Y
          %%
          ",
        )
        .unwrap();
        assert_eq!(
            ast.implicit_tokens,
            Some(["X".to_string(), "Y".to_string()].iter().cloned().collect())
        );
    }

    #[test]
    fn test_duplicate_implicit_tokens() {
        match parse(
            YaccKind::Eco,
            &"
          %implicit_tokens X
          %implicit_tokens X Y
          %%
          ",
        ) {
            Ok(_) => panic!(),
            Err(YaccParserError {
                kind: YaccParserErrorKind::DuplicateImplicitTokensDeclaration,
                line: 3,
                ..
            }) => (),
            Err(e) => panic!("Incorrect error returned {}", e),
        }
    }

    #[test]
    fn test_duplicate_implicit_tokens2() {
        match parse(
            YaccKind::Eco,
            &"
          %implicit_tokens X X
          %implicit_tokens Y
          %%
          ",
        ) {
            Ok(_) => panic!(),
            Err(YaccParserError {
                kind: YaccParserErrorKind::DuplicateImplicitTokensDeclaration,
                line: 2,
                ..
            }) => (),
            Err(e) => panic!("Incorrect error returned {}", e),
        }
    }

    #[test]
    fn test_parse_epp() {
        let ast = parse(
            YaccKind::Eco,
            &"
          %epp A \"a\"
          %epp B 'a'
          %epp C '\"'
          %epp D \"'\"
          %epp E \"\\\"\"
          %epp F '\\''
          %epp G \"a\\\"b\"
          %%
          R: 'A';
          ",
        )
        .unwrap();
        assert_eq!(ast.epp.len(), 7);
        assert_eq!(ast.epp["A"], "a");
        assert_eq!(ast.epp["B"], "a");
        assert_eq!(ast.epp["C"], "\"");
        assert_eq!(ast.epp["D"], "'");
        assert_eq!(ast.epp["E"], "\"");
        assert_eq!(ast.epp["F"], "'");
        assert_eq!(ast.epp["G"], "a\"b");
    }

    #[test]
    fn test_duplicate_epp() {
        match parse(
            YaccKind::Eco,
            &"
          %epp A \"a\"
          %epp A \"a\"
          %%
          ",
        ) {
            Ok(_) => panic!(),
            Err(YaccParserError {
                kind: YaccParserErrorKind::DuplicateEPP,
                line: 3,
                ..
            }) => (),
            Err(e) => panic!("Incorrect error returned {}", e),
        }
    }

    #[test]
    fn test_broken_string() {
        match parse(
            YaccKind::Eco,
            &"
          %epp A \"a
          %%
          ",
        ) {
            Ok(_) => panic!(),
            Err(YaccParserError {
                kind: YaccParserErrorKind::InvalidString,
                line: 2,
                ..
            }) => (),
            Err(e) => panic!("Incorrect error returned {}", e),
        }

        match parse(
            YaccKind::Eco,
            &"
          %epp A \"a",
        ) {
            Ok(_) => panic!(),
            Err(YaccParserError {
                kind: YaccParserErrorKind::InvalidString,
                line: 2,
                ..
            }) => (),
            Err(e) => panic!("Incorrect error returned {}", e),
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
          ",
        ) {
            Ok(_) => panic!(),
            Err(YaccParserError {
                kind: YaccParserErrorKind::DuplicateStartDeclaration,
                line: 3,
                ..
            }) => (),
            Err(e) => panic!("Incorrect error returned {}", e),
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
          ",
        )
        .unwrap();
        assert_eq!(ast.start, Some("R".to_string()));
    }

    #[test]
    fn test_action() {
        let grm = parse(
            YaccKind::Original(YaccOriginalActionKind::GenericParseTree),
            &"
          %%
          A: 'a' B { println!(\"test\"); }
           ;
          B: 'b' 'c' { add($1, $2); }
           | 'd'
           ;
          ",
        )
        .unwrap();
        assert_eq!(
            grm.prods[grm.rules["A"].pidxs[0]].action,
            Some("println!(\"test\");".to_string())
        );
        assert_eq!(
            grm.prods[grm.rules["B"].pidxs[0]].action,
            Some("add($1, $2);".to_string())
        );
        assert_eq!(grm.prods[grm.rules["B"].pidxs[1]].action, None);
    }

    #[test]
    fn test_programs() {
        let grm = parse(
            YaccKind::Original(YaccOriginalActionKind::GenericParseTree),
            &"
         %%
         A: 'a';
         %%
         fn foo() {}",
        )
        .unwrap();
        assert_eq!(grm.programs, Some("fn foo() {}".to_string()));
    }

    #[test]
    fn test_actions_with_newlines() {
        match parse(
            YaccKind::Original(YaccOriginalActionKind::GenericParseTree),
            &"
         %%
         A: 'a' { foo();
                  bar(); }
         ;
         B: b';",
        ) {
            Ok(_) => panic!(),
            Err(YaccParserError { line: 6, .. }) => (),
            Err(e) => panic!("Incorrect error returned {}", e),
        }
    }

    #[test]
    fn test_comments() {
        let src = "
            // A valid comment
            %token   a
            /* Another valid comment */
            %%\n
            A : a;";
        let grm = parse(
            YaccKind::Original(YaccOriginalActionKind::GenericParseTree),
            src,
        )
        .unwrap();
        assert!(grm.has_token("a"));

        match parse(
            YaccKind::Original(YaccOriginalActionKind::GenericParseTree),
            &"
            /* An invalid comment * /
            %token   a
            %%\n
            A : a;",
        ) {
            Ok(_) => panic!(),
            Err(YaccParserError {
                kind: YaccParserErrorKind::IncompleteComment,
                line: 2,
                ..
            }) => (),
            Err(e) => panic!("Incorrect error returned {}", e),
        }

        match parse(
            YaccKind::Original(YaccOriginalActionKind::GenericParseTree),
            &"
            %token   a
            %%
            /* A valid
             * multi-line comment
             */
            /* An invalid comment * /
            A : a;",
        ) {
            Ok(_) => panic!(),
            Err(YaccParserError {
                kind: YaccParserErrorKind::IncompleteComment,
                line: 7,
                ..
            }) => (),
            Err(e) => panic!("Incorrect error returned {}", e),
        }

        match parse(
            YaccKind::Original(YaccOriginalActionKind::GenericParseTree),
            &"
            %token   a
            %%
            // Valid comment
            A : a",
        ) {
            Ok(_) => panic!(),
            Err(YaccParserError {
                kind: YaccParserErrorKind::IncompleteRule,
                line: 5,
                ..
            }) => (),
            Err(e) => panic!("Incorrect error returned {}", e),
        }
    }

    #[test]
    fn test_action_type() {
        let grm = parse(
            YaccKind::Original(YaccOriginalActionKind::UserAction),
            &"
         %actiontype T
         %%
         A: 'a';
         %%
         fn foo() {}",
        )
        .unwrap();
        assert_eq!(grm.rules["A"].actiont, Some("T".to_string()));
    }

    #[test]
    fn test_only_one_type() {
        match parse(
            YaccKind::Original(YaccOriginalActionKind::GenericParseTree),
            &"
         %actiontype T1
         %actiontype T2
         %%
         A: 'a';",
        ) {
            Ok(_) => panic!(),
            Err(YaccParserError {
                line: 3,
                kind: YaccParserErrorKind::DuplicateActiontypeDeclaration,
                ..
            }) => (),
            Err(e) => panic!("Incorrect error returned {}", e),
        }
    }

    #[test]
    fn test_parse_param() {
        let src = "
          %parse_param <'a, 'b> (x: &'a (), (y, z) : (Result<((), ()), ((), ())>, ((u32, u32), &'b ())))
          %%
          A: 'a';
         ";
        let grm = parse(
            YaccKind::Original(YaccOriginalActionKind::GenericParseTree),
            &src,
        )
        .unwrap();

        let expect_lifetimes = HashSet::from_iter([&"'a", &"'b"].iter().map(|s| s.to_string()));
        let expect_bindings = [
            ("x", "&'a ()"),
            (
                "(y, z)",
                "(Result<((), ()), ((), ())>, ((u32, u32), &'b ()))",
            ),
        ]
        .iter()
        .map(|(v, t)| (v.to_string(), t.to_string()))
        .collect::<Vec<(String, String)>>();
        assert_eq!(grm.parse_param_lifetimes, Some(expect_lifetimes));
        assert_eq!(grm.parse_param_bindings, Some(expect_bindings));
    }
}
