// Note: this is the parser for both YaccKind::Original(YaccOriginalActionKind::GenericParseTree) and YaccKind::Eco yacc kinds.

use std::{collections::HashSet, error::Error, fmt, str::FromStr};

use lazy_static::lazy_static;
use num_traits::PrimInt;
use regex::Regex;

type YaccResult<T> = Result<T, YaccParserError>;

use crate::Span;

use super::{
    ast::{GrammarAST, Symbol},
    AssocKind, Precedence, YaccKind,
};

/// The various different possible Yacc parser errors.
#[derive(Debug)]
pub enum YaccParserErrorKind {
    IllegalInteger,
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
    DuplicateExpectDeclaration,
    DuplicateExpectRRDeclaration,
    DuplicateStartDeclaration,
    DuplicateActiontypeDeclaration,
    DuplicateEPP,
    ReachedEOL,
    InvalidString,
}

#[derive(Debug)]
pub enum YaccParserAdditionalErrorKind {
    /// This kind correlates to an existing YaccParserErrorKind.
    Error(YaccParserErrorKind),
    /// A more specialized error kind which may not be a valid top-level error kind.
    Specialized(YaccParserSpecializedErrorKind),
}

#[non_exhaustive]
#[derive(Debug)]
pub enum YaccParserSpecializedErrorKind {
    OriginalDeclaration,
}

/// Any error from the Yacc parser returns an instance of this struct.
#[derive(Debug)]
pub struct YaccParserError {
    pub kind: YaccParserErrorKind,
    pub span: Span,
    pub related_errors: Vec<(YaccParserAdditionalErrorKind, Span)>,
}

impl Error for YaccParserError {}

impl fmt::Display for YaccParserError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.kind)
    }
}
impl fmt::Display for YaccParserErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let s = match self {
            YaccParserErrorKind::IllegalInteger => "Illegal integer",
            YaccParserErrorKind::IllegalName => "Illegal name",
            YaccParserErrorKind::IllegalString => "Illegal string",
            YaccParserErrorKind::IncompleteRule => "Incomplete rule",
            YaccParserErrorKind::DuplicateRule { .. } => "Duplicate rule",
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
            YaccParserErrorKind::DuplicateExpectDeclaration => "Duplicate %expect declaration",
            YaccParserErrorKind::DuplicateExpectRRDeclaration => "Duplicate %expect-rr declaration",
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
        write!(f, "{}", s)
    }
}

impl fmt::Display for YaccParserAdditionalErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let s = match self {
            OriginalDeclaration => "The original declaration",
        };
        write!(f, "{}", s)
    }
}

pub(crate) struct YaccParser {
    yacc_kind: YaccKind,
    src: String,
    num_newlines: usize,
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
            num_newlines: 0,
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
                    let (j, n, span) = self.parse_token(i)?;
                    if self.ast.tokens.insert(n) {
                        self.ast.spans.push(span);
                    }
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
                let (j, n, _) = self.parse_token(i)?;
                if self.ast.epp.contains_key(&n) {
                    return Err(self.mk_error(YaccParserErrorKind::DuplicateEPP, i));
                }
                i = self.parse_ws(j, false)?;
                let (j, v) = self.parse_string(i)?;
                self.ast.epp.insert(n, v);
                i = self.parse_ws(j, true)?;
                continue;
            }
            if let Some(j) = self.lookahead_is("%expect-rr", i) {
                if self.ast.expectrr.is_some() {
                    return Err(self.mk_error(YaccParserErrorKind::DuplicateExpectRRDeclaration, i));
                }
                i = self.parse_ws(j, false)?;
                let (j, n) = self.parse_int(i)?;
                self.ast.expectrr = Some(n);
                i = self.parse_ws(j, true)?;
                continue;
            }
            if let Some(j) = self.lookahead_is("%expect", i) {
                if self.ast.expect.is_some() {
                    return Err(self.mk_error(YaccParserErrorKind::DuplicateExpectDeclaration, i));
                }
                i = self.parse_ws(j, false)?;
                let (j, n) = self.parse_int(i)?;
                self.ast.expect = Some(n);
                i = self.parse_ws(j, true)?;
                continue;
            }
            if let Some(j) = self.lookahead_is("%avoid_insert", i) {
                i = self.parse_ws(j, false)?;
                let num_newlines = self.num_newlines;
                if self.ast.avoid_insert.is_none() {
                    self.ast.avoid_insert = Some(HashSet::new());
                }
                while j < self.src.len() && self.num_newlines == num_newlines {
                    let (j, n, span) = self.parse_token(i)?;
                    if self.ast.tokens.insert(n.clone()) {
                        self.ast.spans.push(span);
                    }
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
            if let Some(j) = self.lookahead_is("%parse-param", i) {
                i = self.parse_ws(j, false)?;
                let (j, name) = self.parse_to_single_colon(i)?;
                match self.lookahead_is(":", j) {
                    Some(j) => i = self.parse_ws(j, false)?,
                    None => {
                        return Err(self.mk_error(YaccParserErrorKind::MissingColon, j));
                    }
                }
                let (j, ty) = self.parse_to_eol(i)?;
                self.ast.parse_param = Some((name, ty));
                i = self.parse_ws(j, true)?;
                continue;
            }
            if let YaccKind::Eco = self.yacc_kind {
                if let Some(j) = self.lookahead_is("%implicit_tokens", i) {
                    i = self.parse_ws(j, false)?;
                    let num_newlines = self.num_newlines;
                    if self.ast.implicit_tokens.is_none() {
                        self.ast.implicit_tokens = Some(HashSet::new());
                    }
                    while j < self.src.len() && self.num_newlines == num_newlines {
                        let (j, n, span) = self.parse_token(i)?;
                        if self.ast.tokens.insert(n.clone()) {
                            self.ast.spans.push(span);
                        }
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
                let num_newlines = self.num_newlines;
                while i < self.src.len() && num_newlines == self.num_newlines {
                    let (j, n, _) = self.parse_token(i)?;
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
        let span = Span::new(i, j);
        match self.yacc_kind {
            YaccKind::Original(_) | YaccKind::Eco => {
                if self.ast.get_rule(&rn).is_none() {
                    self.ast
                        .add_rule((rn.clone(), span), self.global_actiontype.clone());
                }
                i = j;
            }
            YaccKind::Grmtools => {
                if let Some(rule) = self.ast.get_rule(&rn) {
                    let (_, original_span) = rule.name;
                    return Err(YaccParserError {
                        kind: YaccParserErrorKind::DuplicateRule,
                        span,
                        related_errors: vec![(
                            YaccParserAdditionalErrorKind::Specialized(
                                YaccParserSpecializedErrorKind::OriginalDeclaration,
                            ),
                            original_span,
                        )],
                    });
                }
                i = self.parse_ws(j, true)?;
                if let Some(j) = self.lookahead_is("->", i) {
                    i = j;
                } else {
                    return Err(self.mk_error(YaccParserErrorKind::MissingRightArrow, i));
                }
                i = self.parse_ws(i, true)?;
                let (j, actiont) = self.parse_to_single_colon(i)?;
                self.ast.add_rule((rn.clone(), span), Some(actiont));
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
                let (j, sym, span) = self.parse_token(i)?;
                i = self.parse_ws(j, true)?;
                if self.ast.tokens.insert(sym.clone()) {
                    self.ast.spans.push(span);
                }
                syms.push(Symbol::Token(sym, span));
            } else if let Some(j) = self.lookahead_is("%prec", i) {
                i = self.parse_ws(j, true)?;
                let (k, sym, _) = self.parse_token(i)?;
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
                let (j, sym, span) = self.parse_token(i)?;
                if self.ast.tokens.contains(&sym) {
                    syms.push(Symbol::Token(sym, span));
                } else {
                    syms.push(Symbol::Rule(sym, span));
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

    fn parse_token(&self, i: usize) -> YaccResult<(usize, String, Span)> {
        match RE_TOKEN.find(&self.src[i..]) {
            Some(m) => {
                assert!(m.start() == 0 && m.end() > 0);
                match self.src[i..].chars().next().unwrap() {
                    '"' | '\'' => {
                        debug_assert!('"'.len_utf8() == 1 && '\''.len_utf8() == 1);
                        let start_cidx = i + 1;
                        let end_cidx = i + m.end() - 1;
                        Ok((
                            i + m.end(),
                            self.src[start_cidx..end_cidx].to_string(),
                            Span::new(start_cidx, end_cidx),
                        ))
                    }
                    _ => Ok((
                        i + m.end(),
                        self.src[i..i + m.end()].to_string(),
                        Span::new(i, i + m.end()),
                    )),
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
                    self.num_newlines += 1;
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
            let prog = self.src[i..].to_string();
            i += prog.len();
            self.ast.set_programs(prog);
        }
        Ok(i)
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
                    self.num_newlines += 1;
                    j += c.len_utf8();
                }
                _ => j += c.len_utf8(),
            }
        }
        Err(self.mk_error(YaccParserErrorKind::ReachedEOL, j))
    }

    /// Parse a quoted string, allowing escape characters.
    fn parse_int<T: FromStr + PrimInt>(&mut self, i: usize) -> YaccResult<(usize, T)> {
        let mut j = i;
        while j < self.src.len() {
            let c = self.src[j..].chars().next().unwrap();
            match c {
                '0' | '1' | '2' | '3' | '4' | '5' | '6' | '7' | '8' | '9' => j += 1,
                _ => break,
            }
        }
        match self.src[i..j].parse::<T>() {
            Ok(x) => Ok((j, x)),
            Err(_) => Err(self.mk_error(YaccParserErrorKind::IllegalInteger, i)),
        }
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
                    self.num_newlines += 1;
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
                                        self.num_newlines += 1;
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
                                            self.num_newlines += 1;
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
        let span = Span::new(off, off);
        YaccParserError {
            kind: k,
            span,
            related_errors: vec![],
        }
    }
}

#[cfg(test)]
mod test {
    use super::{
        super::{
            ast::{GrammarAST, Production, Symbol},
            AssocKind, Precedence, YaccKind, YaccOriginalActionKind,
        },
        Span, YaccParser, YaccParserError, YaccParserErrorKind,
    };

    fn parse(yacc_kind: YaccKind, s: &str) -> Result<GrammarAST, YaccParserError> {
        let mut yp = YaccParser::new(yacc_kind, s.to_string());
        yp.parse()?;
        Ok(yp.ast())
    }

    fn rule(n: &str) -> Symbol {
        Symbol::Rule(n.to_string(), Span::new(0, 0))
    }

    fn rule_span(n: &str, span: Span) -> Symbol {
        Symbol::Rule(n.to_string(), span)
    }

    fn token(n: &str) -> Symbol {
        Symbol::Token(n.to_string(), Span::new(0, 0))
    }
    fn token_span(n: &str, span: Span) -> Symbol {
        Symbol::Token(n.to_string(), span)
    }

    fn line_of_offset(s: &str, off: usize) -> usize {
        s[..off].lines().count()
    }

    macro_rules! incorrect_err {
        ($src:ident, $e:ident) => {{
            let mut line_cache = crate::newlinecache::NewlineCache::new();
            line_cache.feed(&$src);
            if let Some((line, column)) = line_cache.byte_to_line_and_col(&$src, $e.span.start()) {
                panic!(
                    "Incorrect error returned {} at line {line} column {column}",
                    $e
                )
            } else {
                panic!("Incorrect error returned {} with unknown span", $e)
            }
        }};
    }

    macro_rules! line_col {
        ($src:ident, $span: ident) => {{
            let mut line_cache = crate::newlinecache::NewlineCache::new();
            line_cache.feed(&$src);
            line_cache
                .byte_to_line_and_col(&$src, $span.start())
                .unwrap()
        }};
    }

    #[test]
    fn test_helper_fn() {
        assert_eq!(Symbol::Token("A".to_string(), Span::new(0, 0)), token("A"));
    }

    #[test]
    fn test_symbol_eq() {
        assert_eq!(rule("A"), rule("A"));
        assert_ne!(rule("A"), rule("B"));
        assert_ne!(rule("A"), token("A"));
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
        let a_span = Span::new(33, 34);
        assert_eq!(
            grm.prods[grm.get_rule("A").unwrap().pidxs[0]],
            Production {
                symbols: vec![token_span("a", a_span)],
                precedence: None,
                action: None
            }
        );
        assert_eq!(&src[a_span.start()..a_span.end()], "a");
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
        let a_span = Span::new(33, 34);
        assert_eq!(
            grm.prods[grm.get_rule("A").unwrap().pidxs[0]],
            Production {
                symbols: vec![token_span("a", a_span)],
                precedence: None,
                action: None
            }
        );
        assert_eq!(&src[a_span.start()..a_span.end()], "a");
        let b_span = Span::new(54, 55);
        assert_eq!(
            grm.prods[grm.get_rule("A").unwrap().pidxs[1]],
            Production {
                symbols: vec![token_span("b", Span::new(54, 55))],
                precedence: None,
                action: None
            }
        );
        assert_eq!(&src[b_span.start()..b_span.end()], "b");
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

        let b_span = Span::new(51, 52);
        assert_eq!(
            grm.prods[grm.get_rule("B").unwrap().pidxs[0]],
            Production {
                symbols: vec![token_span("b", b_span)],
                precedence: None,
                action: None
            }
        );
        assert_eq!(&src[b_span.start()..b_span.end()], "b");
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
        let c_span = Span::new(77, 78);
        assert_eq!(
            grm.prods[grm.get_rule("C").unwrap().pidxs[1]],
            Production {
                symbols: vec![token_span("c", c_span)],
                precedence: None,
                action: None
            }
        );
        assert_eq!(&src[c_span.start()..c_span.end()], "c");
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
        let a_span = Span::new(8, 9);
        let b_span = Span::new(11, 12);
        assert_eq!(
            grm.prods[grm.get_rule("A").unwrap().pidxs[0]],
            Production {
                symbols: vec![token_span("a", a_span), rule_span("B", b_span)],
                precedence: None,
                action: None
            }
        );
        assert_eq!(&src[a_span.start()..a_span.end()], "a");
        assert_eq!(&src[b_span.start()..b_span.end()], "B");
    }

    #[test]
    fn test_token_types() {
        let src = "%%\nA : 'a' \"b\";".to_string();
        let grm = parse(
            YaccKind::Original(YaccOriginalActionKind::GenericParseTree),
            &src,
        )
        .unwrap();
        let a_span = Span::new(8, 9);
        let b_span = Span::new(12, 13);
        assert_eq!(
            grm.prods[grm.get_rule("A").unwrap().pidxs[0]],
            Production {
                symbols: vec![token_span("a", a_span), token_span("b", b_span)],
                precedence: None,
                action: None
            }
        );
        assert_eq!(&src[a_span.start()..a_span.end()], "a");
        assert_eq!(&src[b_span.start()..b_span.end()], "b");
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
        let t_span = Span::new(16, 17);
        assert_eq!(
            grm.prods[grm.get_rule("A").unwrap().pidxs[0]],
            Production {
                symbols: vec![token_span("T", t_span)],
                precedence: None,
                action: None
            }
        );
        assert_eq!(&src[t_span.start()..t_span.end() + 1], "T;");
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
                span,
                ..
            }) if line_col!(src, span) == (1, 12) => (),
            Err(e) => incorrect_err!(src, e),
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
                span,
                ..
            }) if line_col!(src, span) == (3, 11) => (),
            Err(e) => incorrect_err!(src, e),
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
                span,
                ..
            }) if line_col!(src, span) == (1, 5) => (),
            Err(e) => incorrect_err!(src, e),
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
                span,
                ..
            }) if line_col!(src, span) == (2, 3) => (),
            Err(e) => incorrect_err!(src, e),
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
                span,
                ..
            }) if line_col!(src, span) == (3, 1) => (),
            Err(e) => incorrect_err!(src, e),
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
                span,
                ..
            }) if line_col!(src, span) == (3, 9) => (),
            Err(e) => incorrect_err!(src, e),
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
                span,
                ..
            }) if line_col!(src, span) == (1, 5) => (),
            Err(e) => incorrect_err!(src, e),
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
                span,
                ..
            }) if line_col!(src, span) == (1, 8) => (),
            Err(e) => incorrect_err!(src, e),
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
                span,
                ..
            }) if line_col!(src, span) == (1, 7) => (),
            Err(e) => incorrect_err!(src, e),
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
                span,
                ..
            }) if line_col!(src, span) == (1, 1) => (),
            Err(e) => incorrect_err!(src, e),
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
                src,
            ) {
                Ok(_) => panic!("Duplicate precedence parsed"),
                Err(YaccParserError {
                    kind: YaccParserErrorKind::DuplicatePrecedence,
                    span,
                    ..
                }) if line_of_offset(src, span.start()) == 3 => (),
                Err(e) => incorrect_err!(src, e),
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
        let grm = parse(YaccKind::Original(YaccOriginalActionKind::GenericParseTree), src).unwrap();
        assert_eq!(grm.precs.len(), 4);
        assert_eq!(grm.prods[grm.rules["expr"].pidxs[0]].precedence, None);
        assert_eq!(grm.prods[grm.rules["expr"].pidxs[3]].symbols.len(), 3);
        assert_eq!(grm.prods[grm.rules["expr"].pidxs[4]].symbols.len(), 2);
        assert_eq!(grm.prods[grm.rules["expr"].pidxs[4]].precedence, Some("*".to_string()));
    }

    #[test]
    fn test_bad_prec_overrides() {
        let src = "
        %%
        S: 'A' %prec ;
        ";
        match parse(
            YaccKind::Original(YaccOriginalActionKind::GenericParseTree),
            src,
        ) {
            Ok(_) => panic!("Incorrect %prec parsed"),
            Err(YaccParserError {
                kind: YaccParserErrorKind::IllegalString,
                span,
                ..
            }) if line_of_offset(src, span.start()) == 3 => (),
            Err(e) => incorrect_err!(src, e),
        }

        let src = "
        %%
        S: 'A' %prec B;
        B: ;
        ";
        match parse(
            YaccKind::Original(YaccOriginalActionKind::GenericParseTree),
            src,
        ) {
            Ok(_) => panic!("Incorrect %prec parsed"),
            Err(YaccParserError {
                kind: YaccParserErrorKind::PrecNotFollowedByToken,
                span,
                ..
            }) if line_of_offset(src, span.start()) == 3 => (),
            Err(e) => incorrect_err!(src, e),
        }
    }

    #[test]
    fn test_parse_avoid_insert() {
        let ast = parse(
            YaccKind::Eco,
            "
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
            "
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
        let src = "
          %avoid_insert X Y
          %avoid_insert Y
          %%
          ";
        match parse(YaccKind::Eco, src) {
            Ok(_) => panic!(),
            Err(YaccParserError {
                kind: YaccParserErrorKind::DuplicateAvoidInsertDeclaration,
                span,
                ..
            }) if line_of_offset(src, span.start()) == 3 => (),
            Err(e) => incorrect_err!(src, e),
        }
    }

    #[test]
    fn test_duplicate_avoid_insert2() {
        let src = "
        %avoid_insert X
        %avoid_insert Y Y
        %%
        ";
        match parse(YaccKind::Eco, src) {
            Ok(_) => panic!(),
            Err(YaccParserError {
                kind: YaccParserErrorKind::DuplicateAvoidInsertDeclaration,
                span,
                ..
            }) if line_of_offset(src, span.start()) == 3 => (),
            Err(e) => incorrect_err!(src, e),
        }
    }

    #[test]
    fn test_no_implicit_tokens_in_original_yacc() {
        let src = "
        %implicit_tokens X
        %%
        ";
        match parse(
            YaccKind::Original(YaccOriginalActionKind::GenericParseTree),
            src,
        ) {
            Ok(_) => panic!(),
            Err(YaccParserError {
                kind: YaccParserErrorKind::UnknownDeclaration,
                span,
                ..
            }) if line_of_offset(src, span.start()) == 2 => (),
            Err(e) => incorrect_err!(src, e),
        }
    }

    #[test]
    fn test_parse_implicit_tokens() {
        let ast = parse(
            YaccKind::Eco,
            "
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
            "
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
        let src = "
        %implicit_tokens X
        %implicit_tokens X Y
        %%
        ";
        match parse(YaccKind::Eco, src) {
            Ok(_) => panic!(),
            Err(YaccParserError {
                kind: YaccParserErrorKind::DuplicateImplicitTokensDeclaration,
                span,
                ..
            }) if line_of_offset(src, span.start()) == 3 => (),
            Err(e) => incorrect_err!(src, e),
        }
    }

    #[test]
    fn test_duplicate_implicit_tokens2() {
        let src = "
        %implicit_tokens X X
        %implicit_tokens Y
        %%
        ";
        match parse(YaccKind::Eco, src) {
            Ok(_) => panic!(),
            Err(YaccParserError {
                kind: YaccParserErrorKind::DuplicateImplicitTokensDeclaration,
                span,
                ..
            }) if line_of_offset(src, span.start()) == 2 => (),
            Err(e) => incorrect_err!(src, e),
        }
    }

    #[test]
    fn test_parse_epp() {
        let ast = parse(
            YaccKind::Eco,
            "
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
        let src = "
        %epp A \"a\"
        %epp A \"a\"
        %%
        ";
        match parse(YaccKind::Eco, src) {
            Ok(_) => panic!(),
            Err(YaccParserError {
                kind: YaccParserErrorKind::DuplicateEPP,
                span,
                ..
            }) if line_of_offset(src, span.start()) == 3 => (),
            Err(e) => incorrect_err!(src, e),
        }
    }

    #[test]
    fn test_broken_string() {
        let src = "
          %epp A \"a
          %%
          ";
        match parse(YaccKind::Eco, src) {
            Ok(_) => panic!(),
            Err(YaccParserError {
                kind: YaccParserErrorKind::InvalidString,
                span,
                ..
            }) if line_of_offset(src, span.start()) == 2 => (),
            Err(e) => incorrect_err!(src, e),
        }
        let src = "
        %epp A \"a";
        match parse(YaccKind::Eco, src) {
            Ok(_) => panic!(),
            Err(YaccParserError {
                kind: YaccParserErrorKind::InvalidString,
                span,
                ..
            }) if line_of_offset(src, span.start()) == 2 => (),
            Err(e) => incorrect_err!(src, e),
        }
    }

    #[test]
    fn test_duplicate_start() {
        let src = "
          %start X
          %start X
          %%
          ";
        match parse(YaccKind::Eco, src) {
            Ok(_) => panic!(),
            Err(YaccParserError {
                kind: YaccParserErrorKind::DuplicateStartDeclaration,
                span,
                ..
            }) if line_of_offset(src, span.start()) == 3 => (),
            Err(e) => incorrect_err!(src, e),
        }
    }

    #[test]
    fn test_implicit_start() {
        let ast = parse(
            YaccKind::Eco,
            "
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
            "
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
            "
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
        let src = "
        %%
        A: 'a' { foo();
                 bar(); }
        ;
        B: b';";
        match parse(
            YaccKind::Original(YaccOriginalActionKind::GenericParseTree),
            src,
        ) {
            Ok(_) => panic!(),
            Err(YaccParserError { span, .. }) if line_of_offset(src, span.start()) == 6 => (),
            Err(e) => incorrect_err!(src, e),
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

        let src = "
        /* An invalid comment * /
        %token   a
        %%\n
        A : a;";
        match parse(
            YaccKind::Original(YaccOriginalActionKind::GenericParseTree),
            src,
        ) {
            Ok(_) => panic!(),
            Err(YaccParserError {
                kind: YaccParserErrorKind::IncompleteComment,
                span,
                ..
            }) if line_of_offset(src, span.start()) == 2 => (),
            Err(e) => incorrect_err!(src, e),
        }

        let src = "
        %token   a
        %%
        /* A valid
         * multi-line comment
         */
        /* An invalid comment * /
        A : a;";
        match parse(
            YaccKind::Original(YaccOriginalActionKind::GenericParseTree),
            src,
        ) {
            Ok(_) => panic!(),
            Err(YaccParserError {
                kind: YaccParserErrorKind::IncompleteComment,
                span,
                ..
            }) if line_of_offset(src, span.start()) == 7 => (),
            Err(e) => incorrect_err!(src, e),
        }

        let src = "
        %token   a
        %%
        // Valid comment
        A : a";
        match parse(
            YaccKind::Original(YaccOriginalActionKind::GenericParseTree),
            src,
        ) {
            Ok(_) => panic!(),
            Err(YaccParserError {
                kind: YaccParserErrorKind::IncompleteRule,
                span,
                ..
            }) if line_of_offset(src, span.start()) == 5 => (),
            Err(e) => incorrect_err!(src, e),
        }
    }

    #[test]
    fn test_action_type() {
        let grm = parse(
            YaccKind::Original(YaccOriginalActionKind::UserAction),
            "
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
        let src = "
         %actiontype T1
         %actiontype T2
         %%
         A: 'a';";
        match parse(
            YaccKind::Original(YaccOriginalActionKind::GenericParseTree),
            src,
        ) {
            Ok(_) => panic!(),
            Err(YaccParserError {
                kind: YaccParserErrorKind::DuplicateActiontypeDeclaration,
                span,
                ..
            }) if line_of_offset(src, span.start()) == 3 => (),
            Err(e) => incorrect_err!(src, e),
        }
    }

    #[test]
    fn test_parse_param() {
        let src = "
          %parse-param a::b: (u64, u64)
          %%
          A: 'a';
         ";
        let grm = parse(YaccKind::Original(YaccOriginalActionKind::UserAction), src).unwrap();

        assert_eq!(
            grm.parse_param,
            Some(("a::b".to_owned(), "(u64, u64)".to_owned()))
        );
    }
}
