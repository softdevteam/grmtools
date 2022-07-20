// Note: this is the parser for both YaccKind::Original(YaccOriginalActionKind::GenericParseTree) and YaccKind::Eco yacc kinds.

use lazy_static::lazy_static;
use num_traits::PrimInt;
use regex::Regex;
use std::{
    collections::{hash_map::Entry, HashMap},
    error::Error,
    fmt,
    str::FromStr,
};

pub type YaccGrammarResult<T> = Result<T, Vec<YaccGrammarError>>;

use crate::Span;

use super::{
    ast::{GrammarAST, Symbol},
    AssocKind, Precedence, YaccKind,
};

/// The various different possible Yacc parser errors.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum YaccGrammarErrorKind {
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
    PrecNotFollowedByToken,
    DuplicatePrecedence,
    DuplicateAvoidInsertDeclaration,
    DuplicateImplicitTokensDeclaration,
    DuplicateExpectDeclaration,
    DuplicateExpectRRDeclaration,
    DuplicateStartDeclaration,
    DuplicateActiontypeDeclaration,
    DuplicateEPP,
    ReachedEOL,
    InvalidString,
    NoStartRule,
    InvalidStartRule(String),
    UnknownRuleRef(String),
    UnknownToken(String),
    NoPrecForToken(String),
    UnknownEPP(String),
}

/// Any error from the Yacc parser returns an instance of this struct.
#[derive(Debug, PartialEq, Eq)]
pub struct YaccGrammarError {
    /// Uniquely identifies each error.
    pub(crate) kind: YaccGrammarErrorKind,
    /// Always contains at least 1 span.
    ///
    /// Refer to [SpansKind] via [spanskind](Self::spanskind)
    /// For meaning and interpretation of spans and their ordering.
    pub(crate) spans: Vec<Span>,
}

impl Error for YaccGrammarError {}

impl fmt::Display for YaccGrammarError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.kind)
    }
}

impl fmt::Display for YaccGrammarErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let s = match self {
            YaccGrammarErrorKind::IllegalInteger => "Illegal integer",
            YaccGrammarErrorKind::IllegalName => "Illegal name",
            YaccGrammarErrorKind::IllegalString => "Illegal string",
            YaccGrammarErrorKind::IncompleteRule => "Incomplete rule",
            YaccGrammarErrorKind::DuplicateRule => "Duplicated rule",
            YaccGrammarErrorKind::IncompleteComment => "Incomplete comment",
            YaccGrammarErrorKind::IncompleteAction => "Incomplete action",
            YaccGrammarErrorKind::MissingColon => "Missing ':'",
            YaccGrammarErrorKind::MissingRightArrow => "Missing '->'",
            YaccGrammarErrorKind::MismatchedBrace => "Mismatched brace",
            YaccGrammarErrorKind::PrematureEnd => "File ends prematurely",
            YaccGrammarErrorKind::ProgramsNotSupported => "Programs not currently supported",
            YaccGrammarErrorKind::UnknownDeclaration => "Unknown declaration",
            YaccGrammarErrorKind::DuplicatePrecedence => "Token has multiple precedences specified",
            YaccGrammarErrorKind::PrecNotFollowedByToken => "%prec not followed by token name",
            YaccGrammarErrorKind::DuplicateAvoidInsertDeclaration => {
                "Duplicated %avoid_insert declaration"
            }
            YaccGrammarErrorKind::DuplicateExpectDeclaration => "Duplicated %expect declaration",
            YaccGrammarErrorKind::DuplicateExpectRRDeclaration => {
                "Duplicate %expect-rr declaration"
            }
            YaccGrammarErrorKind::DuplicateImplicitTokensDeclaration => {
                "Duplicated %implicit_tokens declaration"
            }
            YaccGrammarErrorKind::DuplicateStartDeclaration => "Duplicated %start declaration",
            YaccGrammarErrorKind::DuplicateActiontypeDeclaration => {
                "Duplicate %actiontype declaration"
            }
            YaccGrammarErrorKind::DuplicateEPP => "Duplicate %epp declaration for this token",
            YaccGrammarErrorKind::ReachedEOL => {
                "Reached end of line without finding expected content"
            }
            YaccGrammarErrorKind::InvalidString => "Invalid string",
            YaccGrammarErrorKind::NoStartRule => return write!(f, "No start rule specified"),
            YaccGrammarErrorKind::InvalidStartRule(name) => {
                return write!(f, "Start rule '{}' does not appear in grammar", name)
            }
            YaccGrammarErrorKind::UnknownRuleRef(name) => {
                return write!(f, "Unknown reference to rule '{}'", name)
            }
            YaccGrammarErrorKind::UnknownToken(name) => {
                return write!(f, "Unknown token '{}'", name)
            }
            YaccGrammarErrorKind::NoPrecForToken(name) => {
                return write!(
                    f,
                    "Token '{}' used in %prec has no precedence attached",
                    name
                )
            }
            YaccGrammarErrorKind::UnknownEPP(name) => {
                return write!(f, "Unknown token '{}' in %epp declaration", name)
            }
        };
        write!(f, "{}", s)
    }
}

/// Indicates how to interpret the spans of an error.
pub enum SpansKind {
    /// The first span is the first occurrence, and a span for each subsequent occurrence.
    DuplicationError,
    /// Contains a single span at the site of the error.
    Error,
}

impl YaccGrammarError {
    /// Returns the spans associated with the error, always containing at least 1 span.
    ///
    /// Refer to [SpansKind] via [spanskind](Self::spanskind)
    /// for the meaning and interpretation of spans and their ordering.
    pub fn spans(&self) -> impl Iterator<Item = Span> + '_ {
        self.spans.iter().copied()
    }

    /// Returns the [SpansKind] associated with this error.
    pub fn spanskind(&self) -> SpansKind {
        match self.kind {
            YaccGrammarErrorKind::IllegalInteger
            | YaccGrammarErrorKind::IllegalName
            | YaccGrammarErrorKind::IllegalString
            | YaccGrammarErrorKind::IncompleteRule
            | YaccGrammarErrorKind::IncompleteComment
            | YaccGrammarErrorKind::IncompleteAction
            | YaccGrammarErrorKind::MissingColon
            | YaccGrammarErrorKind::MissingRightArrow
            | YaccGrammarErrorKind::MismatchedBrace
            | YaccGrammarErrorKind::PrematureEnd
            | YaccGrammarErrorKind::PrecNotFollowedByToken
            | YaccGrammarErrorKind::ProgramsNotSupported
            | YaccGrammarErrorKind::UnknownDeclaration
            | YaccGrammarErrorKind::ReachedEOL
            | YaccGrammarErrorKind::InvalidString
            | YaccGrammarErrorKind::NoStartRule
            | YaccGrammarErrorKind::InvalidStartRule(_)
            | YaccGrammarErrorKind::UnknownRuleRef(_)
            | YaccGrammarErrorKind::UnknownToken(_)
            | YaccGrammarErrorKind::NoPrecForToken(_)
            | YaccGrammarErrorKind::UnknownEPP(_) => SpansKind::Error,
            YaccGrammarErrorKind::DuplicateRule
            | YaccGrammarErrorKind::DuplicatePrecedence
            | YaccGrammarErrorKind::DuplicateAvoidInsertDeclaration
            | YaccGrammarErrorKind::DuplicateExpectDeclaration
            | YaccGrammarErrorKind::DuplicateExpectRRDeclaration
            | YaccGrammarErrorKind::DuplicateImplicitTokensDeclaration
            | YaccGrammarErrorKind::DuplicateStartDeclaration
            | YaccGrammarErrorKind::DuplicateActiontypeDeclaration
            | YaccGrammarErrorKind::DuplicateEPP => SpansKind::DuplicationError,
        }
    }
}

pub(crate) struct YaccParser {
    yacc_kind: YaccKind,
    src: String,
    num_newlines: usize,
    ast: GrammarAST,
    global_actiontype: Option<(String, Span)>,
    /// The key is the span of the [Rule](crate::yacc::ast::Rule) being duplicated.
    /// The value contains one span for every duplicate of the key.
    duplicate_rule_spans: HashMap<Span, Vec<Span>>,
    duplicate_avoid_insert_spans: HashMap<Span, Vec<Span>>,
    duplicate_precedence_spans: HashMap<Span, Vec<Span>>,
    duplicate_implicit_token_spans: HashMap<Span, Vec<Span>>,
    duplicate_expect_declarations: Option<(Span, Vec<Span>)>,
    duplicate_expectrr_declarations: Option<(Span, Vec<Span>)>,
    duplicate_start_declarations: Option<(Span, Vec<Span>)>,
    duplicate_actiontype_declarations: Option<Vec<Span>>,
    duplicate_epp_declarations: HashMap<Span, Vec<Span>>,
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
            duplicate_rule_spans: HashMap::new(),
            duplicate_avoid_insert_spans: HashMap::new(),
            duplicate_precedence_spans: HashMap::new(),
            duplicate_implicit_token_spans: HashMap::new(),
            duplicate_expect_declarations: None,
            duplicate_expectrr_declarations: None,
            duplicate_start_declarations: None,
            duplicate_actiontype_declarations: None,
            duplicate_epp_declarations: HashMap::new(),
        }
    }

    pub(crate) fn parse(&mut self) -> YaccGrammarResult<usize> {
        // We pass around an index into the *bytes* of self.src. We guarantee that at all times
        // this points to the beginning of a UTF-8 character (since multibyte characters exist, not
        // every byte within the string is also a valid character).
        let mut i = self.parse_declarations(0).map_err(|e| vec![e]);
        if let Some((orig_span, spans)) = self.duplicate_avoid_insert_spans.iter().next() {
            let mut tmp = vec![*orig_span];
            tmp.extend(spans);
            return Err(vec![YaccGrammarError {
                kind: YaccGrammarErrorKind::DuplicateAvoidInsertDeclaration,
                spans: tmp,
            }]);
        }
        if let Some((orig_span, spans)) = self.duplicate_precedence_spans.iter().next() {
            let mut tmp = vec![*orig_span];
            tmp.extend(spans);
            return Err(vec![YaccGrammarError {
                kind: YaccGrammarErrorKind::DuplicatePrecedence,
                spans: tmp,
            }]);
        }
        if let Some((orig_span, spans)) = self.duplicate_implicit_token_spans.iter().next() {
            let mut tmp = vec![*orig_span];
            tmp.extend(spans);
            return Err(vec![YaccGrammarError {
                kind: YaccGrammarErrorKind::DuplicateImplicitTokensDeclaration,
                spans: tmp,
            }]);
        }
        if let Some((orig_span, spans)) = &self.duplicate_expect_declarations {
            let mut tmp = vec![*orig_span];
            tmp.extend(spans);
            return Err(vec![YaccGrammarError {
                kind: YaccGrammarErrorKind::DuplicateExpectDeclaration,
                spans: tmp,
            }]);
        }
        if let Some((orig_span, spans)) = &self.duplicate_expectrr_declarations {
            let mut tmp = vec![*orig_span];
            tmp.extend(spans);
            return Err(vec![YaccGrammarError {
                kind: YaccGrammarErrorKind::DuplicateExpectRRDeclaration,
                spans: tmp,
            }]);
        }
        if let Some((orig_span, spans)) = &self.duplicate_start_declarations {
            let mut tmp = vec![*orig_span];
            tmp.extend(spans);
            return Err(vec![YaccGrammarError {
                kind: YaccGrammarErrorKind::DuplicateStartDeclaration,
                spans: tmp,
            }]);
        }
        if let Some((orig_span, spans)) = self.duplicate_epp_declarations.iter().next() {
            let mut tmp = vec![*orig_span];
            tmp.extend(spans);
            return Err(vec![YaccGrammarError {
                kind: YaccGrammarErrorKind::DuplicateEPP,
                spans: tmp,
            }]);
        }
        if let Some(spans) = &self.duplicate_actiontype_declarations {
            let orig_span = *self
                .global_actiontype
                .as_ref()
                .map(|(_, span)| span)
                .unwrap();
            let mut tmp = vec![orig_span];
            tmp.extend(spans);
            return Err(vec![YaccGrammarError {
                kind: YaccGrammarErrorKind::DuplicateActiontypeDeclaration,
                spans: tmp,
            }]);
        }
        i = self.parse_rules(i?).map_err(|e| vec![e]);
        if let Some((orig_span, spans)) = self.duplicate_rule_spans.iter().next() {
            let mut tmp = vec![*orig_span];
            tmp.extend(spans);
            return Err(vec![YaccGrammarError {
                kind: YaccGrammarErrorKind::DuplicateRule,
                spans: tmp,
            }]);
        }
        self.parse_programs(i?).map_err(|e| vec![e])
    }

    pub(crate) fn ast(self) -> GrammarAST {
        self.ast
    }

    fn parse_declarations(&mut self, mut i: usize) -> Result<usize, YaccGrammarError> {
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
                    i = self.parse_ws(j, false)?;
                    let (j, n) = self.parse_to_eol(i)?;
                    let span = Span::new(i, j);
                    if self.global_actiontype.is_some() {
                        self.duplicate_actiontype_declarations
                            .get_or_insert_with(Vec::new)
                            .push(span);
                    } else {
                        self.global_actiontype = Some((n, span));
                    }
                    i = self.parse_ws(j, true)?;
                    continue;
                }
            }
            if let Some(j) = self.lookahead_is("%start", i) {
                i = self.parse_ws(j, false)?;
                let (j, n) = self.parse_name(i)?;
                let span = Span::new(i, j);
                if let Some((_, orig_span)) = self.ast.start {
                    self.duplicate_start_declarations
                        .get_or_insert_with(|| (orig_span, Vec::new()))
                        .1
                        .push(span)
                } else {
                    self.ast.start = Some((n, span));
                }
                i = self.parse_ws(j, true)?;
                continue;
            }
            if let Some(j) = self.lookahead_is("%epp", i) {
                i = self.parse_ws(j, false)?;
                let (j, n, _) = self.parse_token(i)?;
                let span = Span::new(i, j);
                i = self.parse_ws(j, false)?;
                let (j, v) = self.parse_string(i)?;
                let vspan = Span::new(i, j);
                match self.ast.epp.entry(n) {
                    Entry::Occupied(orig) => self
                        .duplicate_epp_declarations
                        .entry(orig.get().0)
                        .or_insert_with(Vec::new)
                        .push(span),
                    Entry::Vacant(epp) => {
                        epp.insert((span, (v, vspan)));
                    }
                }
                i = self.parse_ws(j, true)?;
                continue;
            }
            if let Some(j) = self.lookahead_is("%expect-rr", i) {
                i = self.parse_ws(j, false)?;
                let (j, n) = self.parse_int(i)?;
                let span = Span::new(i, j);
                if let Some((_, orig_span)) = self.ast.expectrr {
                    self.duplicate_expectrr_declarations
                        .get_or_insert_with(|| (orig_span, Vec::new()))
                        .1
                        .push(span)
                } else {
                    self.ast.expectrr = Some((n, span));
                }
                i = self.parse_ws(j, true)?;
                continue;
            }
            if let Some(j) = self.lookahead_is("%expect", i) {
                i = self.parse_ws(j, false)?;
                let (j, n) = self.parse_int(i)?;
                let span = Span::new(i, j);
                if let Some((_, orig_span)) = self.ast.expect {
                    self.duplicate_expect_declarations
                        .get_or_insert_with(|| (orig_span, Vec::new()))
                        .1
                        .push(span)
                } else {
                    self.ast.expect = Some((n, span));
                }
                i = self.parse_ws(j, true)?;
                continue;
            }
            if let Some(j) = self.lookahead_is("%avoid_insert", i) {
                i = self.parse_ws(j, false)?;
                let num_newlines = self.num_newlines;
                if self.ast.avoid_insert.is_none() {
                    self.ast.avoid_insert = Some(HashMap::new());
                }
                while j < self.src.len() && self.num_newlines == num_newlines {
                    let (j, n, span) = self.parse_token(i)?;
                    if self.ast.tokens.insert(n.clone()) {
                        self.ast.spans.push(span);
                    }

                    match self.ast.avoid_insert.as_mut().unwrap().entry(n) {
                        Entry::Occupied(occupied) => {
                            self.duplicate_avoid_insert_spans
                                .entry(*occupied.get())
                                .or_insert_with(Vec::new)
                                .push(span);
                        }
                        Entry::Vacant(vacant) => {
                            vacant.insert(span);
                        }
                    }
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
                        return Err(self.mk_error(YaccGrammarErrorKind::MissingColon, j));
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
                        self.ast.implicit_tokens = Some(HashMap::new());
                    }
                    while j < self.src.len() && self.num_newlines == num_newlines {
                        let (j, n, span) = self.parse_token(i)?;
                        if self.ast.tokens.insert(n.clone()) {
                            self.ast.spans.push(span);
                        }
                        match self.ast.implicit_tokens.as_mut().unwrap().entry(n) {
                            Entry::Occupied(entry) => {
                                self.duplicate_implicit_token_spans
                                    .entry(*entry.get())
                                    .or_insert_with(Vec::new)
                                    .push(span);
                            }
                            Entry::Vacant(entry) => {
                                entry.insert(span);
                            }
                        }
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
                    return Err(self.mk_error(YaccGrammarErrorKind::UnknownDeclaration, i));
                }

                i = self.parse_ws(k, false)?;
                let num_newlines = self.num_newlines;
                while i < self.src.len() && num_newlines == self.num_newlines {
                    let (j, n, span) = self.parse_token(i)?;
                    match self.ast.precs.entry(n) {
                        Entry::Occupied(orig) => {
                            let (_, orig_span) = orig.get();
                            self.duplicate_precedence_spans
                                .entry(*orig_span)
                                .or_insert_with(Vec::new)
                                .push(span);
                        }
                        Entry::Vacant(entry) => {
                            let prec = Precedence {
                                level: prec_level,
                                kind,
                            };
                            entry.insert((prec, span));
                        }
                    }

                    i = self.parse_ws(j, true)?;
                }
                prec_level += 1;
            }
        }
        Err(self.mk_error(YaccGrammarErrorKind::PrematureEnd, i - 1))
    }

    fn parse_rules(&mut self, mut i: usize) -> Result<usize, YaccGrammarError> {
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

    fn parse_rule(&mut self, mut i: usize) -> Result<usize, YaccGrammarError> {
        let (j, rn) = self.parse_name(i)?;
        let span = Span::new(i, j);
        if self.ast.start.is_none() {
            self.ast.start = Some((rn.clone(), span));
        }
        match self.yacc_kind {
            YaccKind::Original(_) | YaccKind::Eco => {
                if self.ast.get_rule(&rn).is_none() {
                    self.ast.add_rule(
                        (rn.clone(), span),
                        self.global_actiontype.clone().map(|(s, _)| s),
                    );
                }
                i = j;
            }
            YaccKind::Grmtools => {
                i = self.parse_ws(j, true)?;
                if let Some(j) = self.lookahead_is("->", i) {
                    i = j;
                } else {
                    return Err(self.mk_error(YaccGrammarErrorKind::MissingRightArrow, i));
                }
                i = self.parse_ws(i, true)?;
                let (j, actiont) = self.parse_to_single_colon(i)?;
                match self.ast.get_rule(&rn) {
                    None => self.ast.add_rule((rn.clone(), span), Some(actiont)),
                    Some(orig) => self
                        .duplicate_rule_spans
                        .entry(orig.name.1)
                        .or_insert_with(Vec::new)
                        .push(span),
                }
                i = j;
            }
        }
        i = self.parse_ws(i, true)?;
        match self.lookahead_is(":", i) {
            Some(j) => i = j,
            None => {
                return Err(self.mk_error(YaccGrammarErrorKind::MissingColon, i));
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
                    return Err(self.mk_error(YaccGrammarErrorKind::PrecNotFollowedByToken, i));
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
        Err(self.mk_error(YaccGrammarErrorKind::IncompleteRule, i))
    }

    fn parse_name(&self, i: usize) -> Result<(usize, String), YaccGrammarError> {
        match RE_NAME.find(&self.src[i..]) {
            Some(m) => {
                assert_eq!(m.start(), 0);
                Ok((i + m.end(), self.src[i..i + m.end()].to_string()))
            }
            None => Err(self.mk_error(YaccGrammarErrorKind::IllegalName, i)),
        }
    }

    fn parse_token(&self, i: usize) -> Result<(usize, String, Span), YaccGrammarError> {
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
            None => Err(self.mk_error(YaccGrammarErrorKind::IllegalString, i)),
        }
    }

    fn parse_action(&mut self, i: usize) -> Result<(usize, String), YaccGrammarError> {
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
            Err(self.mk_error(YaccGrammarErrorKind::IncompleteAction, j))
        } else {
            let s = self.src[i + 1..j - 1].trim().to_string();
            Ok((j + 1, s))
        }
    }

    fn parse_programs(&mut self, mut i: usize) -> Result<usize, YaccGrammarError> {
        if let Some(j) = self.lookahead_is("%%", i) {
            i = self.parse_ws(j, true)?;
            let prog = self.src[i..].to_string();
            i += prog.len();
            self.ast.set_programs(prog);
        }
        Ok(i)
    }

    /// Parse up to (but do not include) the end of line (or, if it comes sooner, the end of file).
    fn parse_to_eol(&mut self, i: usize) -> Result<(usize, String), YaccGrammarError> {
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
    fn parse_to_single_colon(&mut self, i: usize) -> Result<(usize, String), YaccGrammarError> {
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
        Err(self.mk_error(YaccGrammarErrorKind::ReachedEOL, j))
    }

    /// Parse a quoted string, allowing escape characters.
    fn parse_int<T: FromStr + PrimInt>(
        &mut self,
        i: usize,
    ) -> Result<(usize, T), YaccGrammarError> {
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
            Err(_) => Err(self.mk_error(YaccGrammarErrorKind::IllegalInteger, i)),
        }
    }

    /// Parse a quoted string, allowing escape characters.
    fn parse_string(&mut self, mut i: usize) -> Result<(usize, String), YaccGrammarError> {
        let qc = if self.lookahead_is("'", i).is_some() {
            '\''
        } else if self.lookahead_is("\"", i).is_some() {
            '"'
        } else {
            return Err(self.mk_error(YaccGrammarErrorKind::InvalidString, i));
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
                    return Err(self.mk_error(YaccGrammarErrorKind::InvalidString, j));
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
                            return Err(self.mk_error(YaccGrammarErrorKind::InvalidString, j));
                        }
                    }
                }
                _ => j += c.len_utf8(),
            }
        }
        Err(self.mk_error(YaccGrammarErrorKind::InvalidString, j))
    }

    /// Skip whitespace from `i` onwards. If `inc_newlines` is `false`, will return `Err` if a
    /// newline is encountered; otherwise newlines are consumed and skipped.
    fn parse_ws(&mut self, mut i: usize, inc_newlines: bool) -> Result<usize, YaccGrammarError> {
        while i < self.src.len() {
            let c = self.src[i..].chars().next().unwrap();
            match c {
                ' ' | '\t' => i += c.len_utf8(),
                '\n' | '\r' => {
                    if !inc_newlines {
                        return Err(self.mk_error(YaccGrammarErrorKind::ReachedEOL, i));
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
                                                return Err(self.mk_error(
                                                    YaccGrammarErrorKind::ReachedEOL,
                                                    i,
                                                ));
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
                                        self.mk_error(YaccGrammarErrorKind::IncompleteComment, i)
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

    fn mk_error(&self, k: YaccGrammarErrorKind, off: usize) -> YaccGrammarError {
        let span = Span::new(off, off);
        YaccGrammarError {
            kind: k,
            spans: vec![span],
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
        Span, YaccGrammarError, YaccGrammarErrorKind, YaccParser,
    };

    fn parse(yacc_kind: YaccKind, s: &str) -> Result<GrammarAST, Vec<YaccGrammarError>> {
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

    macro_rules! incorrect_errs {
        ($src:ident, $es:expr) => {{
            let mut line_cache = crate::newlinecache::NewlineCache::new();
            line_cache.feed(&$src);
            for e in $es {
                if let Some((line, column)) =
                    line_cache.byte_to_line_num_and_col_num(&$src, e.spans.first().unwrap().start())
                {
                    eprintln!(
                        "Incorrect error returned {} at line {line} column {column}",
                        e
                    )
                } else {
                    eprintln!("Incorrect error returned {} with unknown span", e)
                }
            }
            panic!()
        }};
    }

    macro_rules! line_col {
        ($src:ident, $span: expr) => {{
            let mut line_cache = crate::newlinecache::NewlineCache::new();
            line_cache.feed(&$src);
            line_cache
                .byte_to_line_num_and_col_num(&$src, $span.start())
                .unwrap()
        }};
    }

    trait ErrorsHelper {
        fn expect_error_at_line(self, src: &str, kind: YaccGrammarErrorKind, line: usize);
        fn expect_error_at_line_col(
            self,
            src: &str,
            kind: YaccGrammarErrorKind,
            line: usize,
            col: usize,
        );
        fn expect_error_at_lines_cols(
            self,
            src: &str,
            kind: YaccGrammarErrorKind,
            lines_cols: &mut dyn Iterator<Item = (usize, usize)>,
        );
    }

    impl ErrorsHelper for Result<GrammarAST, Vec<YaccGrammarError>> {
        fn expect_error_at_line(self, src: &str, kind: YaccGrammarErrorKind, line: usize) {
            match self.as_ref().map_err(Vec::as_slice) {
                Ok(_) => panic!("Parsed ok while expecting error"),
                Err([e])
                    if e.kind == kind
                        && line_of_offset(src, e.spans().next().unwrap().start()) == line
                        && e.spans.len() == 1 => {}
                Err(e) => incorrect_errs!(src, e),
            }
        }

        fn expect_error_at_line_col(
            self,
            src: &str,
            kind: YaccGrammarErrorKind,
            line: usize,
            col: usize,
        ) {
            self.expect_error_at_lines_cols(src, kind, &mut std::iter::once((line, col)))
        }

        fn expect_error_at_lines_cols(
            self,
            src: &str,
            kind: YaccGrammarErrorKind,
            lines_cols: &mut dyn Iterator<Item = (usize, usize)>,
        ) {
            match self.as_ref().map_err(Vec::as_slice) {
                Ok(_) => panic!("Parsed ok while expecting error"),
                Err([e])
                    if e.kind == kind
                        && line_col!(src, e.spans().next().unwrap())
                            == lines_cols.next().unwrap() =>
                {
                    assert_eq!(
                        e.spans()
                            .skip(1)
                            .map(|span| line_col!(src, span))
                            .collect::<Vec<(usize, usize)>>(),
                        lines_cols.collect::<Vec<(usize, usize)>>()
                    )
                }
                Err(e) => incorrect_errs!(src, e),
            }
        }
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
        assert_eq!(grm.start.unwrap(), ("A".to_string(), Span::new(9, 10)));
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
        parse(
            YaccKind::Original(YaccOriginalActionKind::GenericParseTree),
            &src,
        )
        .expect_error_at_line_col(&src, YaccGrammarErrorKind::IllegalString, 1, 12);
    }

    #[test]
    fn test_unicode_err2() {
        let src = "%token '❤'\n%%\nA : '❤' | ❤;".to_string();
        parse(
            YaccKind::Original(YaccOriginalActionKind::GenericParseTree),
            &src,
        )
        .expect_error_at_line_col(&src, YaccGrammarErrorKind::IllegalString, 3, 11);
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
        parse(
            YaccKind::Original(YaccOriginalActionKind::GenericParseTree),
            &src,
        )
        .expect_error_at_line_col(&src, YaccGrammarErrorKind::IncompleteRule, 1, 5);
    }

    #[test]
    fn test_line_col_report1() {
        let src = "%%
A:"
        .to_string();
        parse(
            YaccKind::Original(YaccOriginalActionKind::GenericParseTree),
            &src,
        )
        .expect_error_at_line_col(&src, YaccGrammarErrorKind::IncompleteRule, 2, 3);
    }

    #[test]
    fn test_line_col_report2() {
        let src = "%%
A:
"
        .to_string();
        parse(
            YaccKind::Original(YaccOriginalActionKind::GenericParseTree),
            &src,
        )
        .expect_error_at_line_col(&src, YaccGrammarErrorKind::IncompleteRule, 3, 1);
    }

    #[test]
    fn test_line_col_report3() {
        let src = "

        %woo"
            .to_string();
        parse(
            YaccKind::Original(YaccOriginalActionKind::GenericParseTree),
            &src,
        )
        .expect_error_at_line_col(&src, YaccGrammarErrorKind::UnknownDeclaration, 3, 9);
    }

    #[test]
    fn test_missing_colon() {
        let src = "%%A x;".to_string();
        parse(
            YaccKind::Original(YaccOriginalActionKind::GenericParseTree),
            &src,
        )
        .expect_error_at_line_col(&src, YaccGrammarErrorKind::MissingColon, 1, 5);
    }

    #[test]
    fn test_premature_end() {
        let src = "%token x".to_string();
        parse(
            YaccKind::Original(YaccOriginalActionKind::GenericParseTree),
            &src,
        )
        .expect_error_at_line_col(&src, YaccGrammarErrorKind::PrematureEnd, 1, 8);
    }

    #[test]
    fn test_same_line() {
        let src = "%token
x"
        .to_string();
        parse(
            YaccKind::Original(YaccOriginalActionKind::GenericParseTree),
            &src,
        )
        .expect_error_at_line_col(&src, YaccGrammarErrorKind::ReachedEOL, 1, 7);
    }

    #[test]
    fn test_unknown_declaration() {
        let src = "%woo".to_string();
        parse(
            YaccKind::Original(YaccOriginalActionKind::GenericParseTree),
            &src,
        )
        .expect_error_at_line_col(&src, YaccGrammarErrorKind::UnknownDeclaration, 1, 1);
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
        assert_eq!(grm.precs["+"], (Precedence{level: 0, kind: AssocKind::Left}, Span::new(18, 19)));
        assert_eq!(grm.precs["-"], (Precedence{level: 0, kind: AssocKind::Left}, Span::new(22, 23)));
        assert_eq!(grm.precs["*"], (Precedence{level: 1, kind: AssocKind::Left}, Span::new(42, 43)));
        assert_eq!(grm.precs["/"], (Precedence{level: 2, kind: AssocKind::Right}, Span::new(63, 64)));
        assert_eq!(grm.precs["^"], (Precedence{level: 3, kind: AssocKind::Right}, Span::new(84, 85)));
        assert_eq!(grm.precs["~"], (Precedence{level: 4, kind: AssocKind::Nonassoc}, Span::new(108, 109)));
    }

    #[test]
    fn test_dup_precs() {
        #[rustfmt::skip]
        let srcs = vec![
            ("
          %left 'x'
          %left 'x'
          %%
          ", ((2, 18), (3, 18))),
            ("
          %left 'x'
          %right 'x'
          %%
          ", ((2, 18), (3, 19))),
            ("
          %right 'x'
          %right 'x'
          %%
          ", ((2, 19), (3, 19))),
            ("
          %nonassoc 'x'
          %nonassoc 'x'
          %%
          ", ((2, 22), (3, 22))),
            ("
          %left 'x'
          %nonassoc 'x'
          %%
          ", ((2, 18), (3, 22))),
            ("
          %right 'x'
          %nonassoc 'x'
          %%
          ", ((2, 19), (3, 22)))
        ];
        for (src, (expected_origin, expected_dup)) in srcs.iter() {
            parse(
                YaccKind::Original(YaccOriginalActionKind::GenericParseTree),
                src,
            )
            .expect_error_at_lines_cols(
                src,
                YaccGrammarErrorKind::DuplicatePrecedence,
                &mut [*expected_origin, *expected_dup].into_iter(),
            );
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
        parse(
            YaccKind::Original(YaccOriginalActionKind::GenericParseTree),
            src,
        )
        .expect_error_at_line(src, YaccGrammarErrorKind::IllegalString, 3);

        let src = "
        %%
        S: 'A' %prec B;
        B: ;
        ";
        parse(
            YaccKind::Original(YaccOriginalActionKind::GenericParseTree),
            src,
        )
        .expect_error_at_line(src, YaccGrammarErrorKind::PrecNotFollowedByToken, 3);
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
                [
                    ("ws1".to_string(), Span::new(25, 28)),
                    ("ws2".to_string(), Span::new(29, 32))
                ]
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
            Some(
                [
                    ("X".to_string(), Span::new(25, 26)),
                    ("Y".to_string(), Span::new(51, 52))
                ]
                .iter()
                .cloned()
                .collect()
            )
        );
    }

    #[test]
    fn test_duplicate_avoid_insert() {
        let src = "
          %avoid_insert X Y
          %avoid_insert Y
          %%
          ";
        parse(YaccKind::Eco, src).expect_error_at_lines_cols(
            src,
            YaccGrammarErrorKind::DuplicateAvoidInsertDeclaration,
            &mut [(2usize, 27usize), (3, 25)].into_iter(),
        );
    }

    #[test]
    fn test_duplicate_avoid_insert2() {
        let src = "
        %avoid_insert X
        %avoid_insert Y Y
        %%
        ";
        parse(YaccKind::Eco, src).expect_error_at_lines_cols(
            src,
            YaccGrammarErrorKind::DuplicateAvoidInsertDeclaration,
            &mut [(3, 23), (3, 25)].into_iter(),
        );
    }

    #[test]
    fn test_no_implicit_tokens_in_original_yacc() {
        let src = "
        %implicit_tokens X
        %%
        ";
        parse(
            YaccKind::Original(YaccOriginalActionKind::GenericParseTree),
            src,
        )
        .expect_error_at_line(src, YaccGrammarErrorKind::UnknownDeclaration, 2);
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
                [
                    ("ws1".to_string(), Span::new(28, 31)),
                    ("ws2".to_string(), Span::new(32, 35))
                ]
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
            Some(
                [
                    ("X".to_string(), Span::new(28, 29)),
                    ("Y".to_string(), Span::new(57, 58))
                ]
                .iter()
                .cloned()
                .collect()
            )
        );
    }

    #[test]
    fn test_duplicate_implicit_tokens() {
        let src = "
        %implicit_tokens X
        %implicit_tokens X Y
        %%
        ";
        parse(YaccKind::Eco, src).expect_error_at_lines_cols(
            src,
            YaccGrammarErrorKind::DuplicateImplicitTokensDeclaration,
            &mut [(2, 26), (3, 26)].into_iter(),
        );
    }

    #[test]
    fn test_duplicate_implicit_tokens2() {
        let src = "
        %implicit_tokens X X
        %implicit_tokens Y
        %%
        ";
        parse(YaccKind::Eco, src).expect_error_at_lines_cols(
            src,
            YaccGrammarErrorKind::DuplicateImplicitTokensDeclaration,
            &mut [(2, 26), (2, 28)].into_iter(),
        );
    }

    #[test]
    #[rustfmt::skip]
    fn test_parse_epp() {
        let ast = parse(
            YaccKind::Eco,
            r#"
          %epp A "a"
          %epp B 'a'
          %epp C '"'
          %epp D "'"
          %epp E "\""
          %epp F '\''
          %epp G "a\"b"
          %%
          R: 'A';
          "#,
        )
        .unwrap();
        assert_eq!(ast.epp.len(), 7);
        assert_eq!(ast.epp["A"], (Span::new(16, 17),   ("a".to_string(),   Span::new(18, 21))));
        assert_eq!(ast.epp["B"], (Span::new(37, 38),   ("a".to_string(),   Span::new(39, 42))));
        assert_eq!(ast.epp["C"], (Span::new(58, 59),   ("\"".to_string(),  Span::new(60, 63))));
        assert_eq!(ast.epp["D"], (Span::new(79, 80),   ("'".to_string(),   Span::new(81, 84))));
        assert_eq!(ast.epp["E"], (Span::new(100, 101), ("\"".to_string(),  Span::new(102, 106))));
        assert_eq!(ast.epp["F"], (Span::new(122, 123), ("'".to_string(),   Span::new(124, 128))));
        assert_eq!(ast.epp["G"], (Span::new(144, 145), ("a\"b".to_string(),Span::new(146, 152))));
    }

    #[test]
    fn test_duplicate_epp() {
        let src = "
        %epp A \"a\"
        %epp A \"a\"
        %epp A \"a\"
        %%
        ";
        parse(YaccKind::Eco, src).expect_error_at_lines_cols(
            src,
            YaccGrammarErrorKind::DuplicateEPP,
            &mut [(2, 14), (3, 14), (4, 14)].into_iter(),
        );
    }

    #[test]
    fn test_broken_string() {
        let src = "
          %epp A \"a
          %%
          ";
        parse(YaccKind::Eco, src).expect_error_at_line(src, YaccGrammarErrorKind::InvalidString, 2);

        let src = "
        %epp A \"a";
        parse(YaccKind::Eco, src).expect_error_at_line(src, YaccGrammarErrorKind::InvalidString, 2);
    }

    #[test]
    fn test_duplicate_start() {
        let src = "
          %start X
          %start X
          %%
          ";
        parse(YaccKind::Eco, src).expect_error_at_lines_cols(
            src,
            YaccGrammarErrorKind::DuplicateStartDeclaration,
            &mut [(2, 18), (3, 18)].into_iter(),
        );
    }

    #[test]
    fn test_duplicate_expect() {
        let src = "
          %expect 1
          %expect 2
          %expect 3
          %%
          ";
        parse(
            YaccKind::Original(YaccOriginalActionKind::GenericParseTree),
            src,
        )
        .expect_error_at_lines_cols(
            src,
            YaccGrammarErrorKind::DuplicateExpectDeclaration,
            &mut [(2, 19), (3, 19), (4, 19)].into_iter(),
        )
    }

    #[test]
    fn test_duplicate_expectrr() {
        let src = "
          %expect-rr 1
          %expect-rr 2
          %expect-rr 3
          %%
          ";
        parse(
            YaccKind::Original(YaccOriginalActionKind::GenericParseTree),
            src,
        )
        .expect_error_at_lines_cols(
            src,
            YaccGrammarErrorKind::DuplicateExpectRRDeclaration,
            &mut [(2, 22), (3, 22), (4, 22)].into_iter(),
        );
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
        assert_eq!(ast.start, Some(("R".to_string(), Span::new(24, 25))));
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
        parse(
            YaccKind::Original(YaccOriginalActionKind::GenericParseTree),
            src,
        )
        .expect_error_at_line(src, YaccGrammarErrorKind::IllegalString, 6);
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
        parse(
            YaccKind::Original(YaccOriginalActionKind::GenericParseTree),
            src,
        )
        .expect_error_at_line(src, YaccGrammarErrorKind::IncompleteComment, 2);

        let src = "
        %token   a
        %%
        /* A valid
         * multi-line comment
         */
        /* An invalid comment * /
        A : a;";
        parse(
            YaccKind::Original(YaccOriginalActionKind::GenericParseTree),
            src,
        )
        .expect_error_at_line(src, YaccGrammarErrorKind::IncompleteComment, 7);

        let src = "
        %token   a
        %%
        // Valid comment
        A : a";
        parse(
            YaccKind::Original(YaccOriginalActionKind::GenericParseTree),
            src,
        )
        .expect_error_at_line(src, YaccGrammarErrorKind::IncompleteRule, 5);
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
         %actiontype T3
         %%
         A: 'a';";
        parse(
            YaccKind::Original(YaccOriginalActionKind::GenericParseTree),
            src,
        )
        .expect_error_at_lines_cols(
            src,
            YaccGrammarErrorKind::DuplicateActiontypeDeclaration,
            &mut [(2, 22), (3, 22), (4, 22)].into_iter(),
        );
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

    #[test]
    fn test_multi_span_error_kinds() {
        let e = parse(
            YaccKind::Grmtools,
            "%start A
             %%
             A -> (): 'a1';
             B -> (): 'bb';
             A -> (): 'a2';
             C -> (): 'cc';
             A -> (): 'a3';
            ",
        )
        .expect_err("parse successful while expecting error");
        assert_eq!(
            e,
            vec![YaccGrammarError {
                kind: YaccGrammarErrorKind::DuplicateRule,
                spans: vec![Span::new(38, 39), Span::new(94, 95), Span::new(150, 151)],
            }]
        );
    }
}
