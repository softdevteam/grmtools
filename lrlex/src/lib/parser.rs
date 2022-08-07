use cfgrammar::Span;
use lazy_static::lazy_static;
use regex::Regex;
use std::borrow::{Borrow as _, Cow};
use std::ops::Not;
use try_from::TryFrom;

use crate::{lexer::Rule, LexBuildError, LexBuildResult, LexErrorKind};

type LexInternalBuildResult<T> = Result<T, LexBuildError>;

lazy_static! {
    static ref RE_START_STATE_NAME: Regex = Regex::new(r"^[a-zA-Z][a-zA-Z0-9_.]*$").unwrap();
    static ref RE_INCLUSIVE_START_STATE_DECLARATION: Regex =
        Regex::new(r"^%[sS][a-zA-Z0-9]*$").unwrap();
    static ref RE_EXCLUSIVE_START_STATE_DECLARATION: Regex =
        Regex::new(r"^%[xX][a-zA-Z0-9]*$").unwrap();
    // Documented in `Escape sequences` in lexcompatibility.m
    static ref RE_LEX_ESC_LITERAL: Regex =
        Regex::new(r"^(([xuU][[:xdigit:]])|[[:digit:]]|[afnrtv\\]|[pP]|[dDsSwW]|[AbBz])").unwrap();
}
const INITIAL_START_STATE_NAME: &str = "INITIAL";

#[derive(Debug)]
#[doc(hidden)]
pub struct StartState {
    /// Associated id of this start state - rules which have this start state
    /// as a prerequisite, or which transition to this start state will store
    /// this id in their appropriate fields.
    pub(super) id: usize,
    /// Name of this start state, as supplied in the declaration section, and
    /// used in prerequisite and target start state sections of the rules.
    pub(super) name: String,
    pub(super) name_span: Span,
    /// If false, a rule with _no_ start state will match when this state is active.
    /// If true, only rules which have include this start state will match when
    /// this state is active.
    pub(super) exclusive: bool,
}

impl StartState {
    pub fn new(id: usize, name: &str, exclusive: bool, name_span: Span) -> Self {
        Self {
            id,
            name: name.to_string(),
            name_span,
            exclusive,
        }
    }
}

pub(super) struct LexParser<StorageT> {
    src: String,
    pub(super) rules: Vec<Rule<StorageT>>,
    pub(super) start_states: Vec<StartState>,
}

fn add_duplicate_occurrence(
    errs: &mut Vec<LexBuildError>,
    kind: LexErrorKind,
    orig_span: Span,
    dup_span: Span,
) {
    if !errs.iter_mut().any(|e| {
        if e.kind == kind && e.spans[0] == orig_span {
            e.spans.push(dup_span);
            true
        } else {
            false
        }
    }) {
        errs.push(LexBuildError {
            kind,
            spans: vec![orig_span, dup_span],
        });
    }
}

impl<StorageT: TryFrom<usize>> LexParser<StorageT> {
    pub(super) fn new(src: String) -> LexBuildResult<LexParser<StorageT>> {
        let mut p = LexParser {
            src,
            rules: Vec::new(),
            start_states: vec![StartState::new(
                0,
                INITIAL_START_STATE_NAME,
                false,
                Span::new(0, 0),
            )],
        };
        p.parse()?;
        Ok(p)
    }

    fn mk_error(&self, kind: LexErrorKind, off: usize) -> LexBuildError {
        let span = Span::new(off, off);
        LexBuildError {
            kind,
            spans: vec![span],
        }
    }

    fn parse(&mut self) -> LexBuildResult<usize> {
        let mut errs = Vec::new();
        let mut i = match self.parse_declarations(0, &mut errs) {
            Ok(i) => i,
            Err(e) => {
                errs.push(e);
                return Err(errs);
            }
        };
        // We don't currently support the subroutines part of a specification. One day we might...
        i = match self.parse_rules(i, &mut errs) {
            Ok(i) => i,
            Err(e) => {
                errs.push(e);
                return Err(errs);
            }
        };

        match self.lookahead_is("%%", i) {
            Some(j) => {
                let k = match self.parse_ws(j) {
                    Ok(k) => k,
                    Err(e) => {
                        errs.push(e);
                        return Err(errs);
                    }
                };
                if k == self.src.len() {
                    if errs.is_empty() {
                        Ok(i)
                    } else {
                        Err(errs)
                    }
                } else {
                    errs.push(self.mk_error(LexErrorKind::RoutinesNotSupported, i));
                    Err(errs)
                }
            }
            None => {
                assert_eq!(i, self.src.len());
                if errs.is_empty() {
                    Ok(i)
                } else {
                    Err(errs)
                }
            }
        }
    }

    fn parse_declarations(
        &mut self,
        mut i: usize,
        errs: &mut Vec<LexBuildError>,
    ) -> LexInternalBuildResult<usize> {
        loop {
            i = self.parse_ws(i)?;
            if i == self.src.len() {
                break Err(self.mk_error(LexErrorKind::PrematureEnd, i - 1));
            }
            if let Some(j) = self.lookahead_is("%%", i) {
                break Ok(j);
            }
            i = self.parse_declaration(i, errs)?;
        }
    }

    fn parse_declaration(
        &mut self,
        i: usize,
        errs: &mut Vec<LexBuildError>,
    ) -> LexInternalBuildResult<usize> {
        let line_len = self.src[i..]
            .find(|c| c == '\n')
            .unwrap_or(self.src.len() - i);
        let line = self.src[i..i + line_len].trim_end();
        let declaration_len = line.find(|c: char| c.is_whitespace()).unwrap_or(line_len);
        let declaration = self.src[i..i + declaration_len].trim_end();
        // Any line beginning with a '%' (percent sign) character and followed by an alphanumeric word
        // beginning with either 's' or 'S' shall define a set of start conditions.
        // Any line beginning with a '%' followed by an alphanumeric word beginning with either
        // 'x' or 'X' shall define a set of exclusive start conditions.
        // The rest of the line, after the first word, is considered to be one or more
        // blank-character-separated names of start conditions.
        if RE_INCLUSIVE_START_STATE_DECLARATION.is_match(declaration) {
            self.declare_start_states(false, i, declaration_len, line_len, errs)
        } else if RE_EXCLUSIVE_START_STATE_DECLARATION.is_match(declaration) {
            self.declare_start_states(true, i, declaration_len, line_len, errs)
        } else {
            Err(self.mk_error(LexErrorKind::UnknownDeclaration, i))
        }
    }

    fn declare_start_states(
        &mut self,
        exclusive: bool,
        off: usize,
        declaration_len: usize,
        line_len: usize,
        errs: &mut Vec<LexBuildError>,
    ) -> LexInternalBuildResult<usize> {
        // Start state declarations are REQUIRED to have at least one start state name
        let declaration_parameters = self.src[off + declaration_len..off + line_len].trim();
        if declaration_parameters.is_empty() {
            return Err(self.mk_error(LexErrorKind::UnknownDeclaration, off));
        }
        let start_states = declaration_parameters
            .split_whitespace()
            .map(|name| {
                let off = name.as_ptr() as usize - self.src.as_ptr() as usize;
                let span = Span::new(off, off + name.len());
                (name, span)
            })
            .collect::<Vec<_>>();

        for (name, name_span) in start_states {
            let id = self.start_states.len();
            if self.validate_start_state(name_span, name, errs)? {
                let start_state = StartState::new(id, name, exclusive, name_span);
                self.start_states.push(start_state);
            }
        }
        Ok(off + line_len)
    }

    /// Validates a `StartState`
    ///
    /// Return `Ok(true)` if the start state is valid.
    ///
    /// A return value of `Ok(false)` indicates the state state is invalid. The site of error will be added to `errs`,
    /// and may be coalesced with related errors.  After which it is safe to continue parsing handling the error
    /// in the future.
    ///
    /// An `Err()` value returned will *not* be added to `errs`.
    fn validate_start_state<'a>(
        &self,
        span: Span,
        name: &'a str,
        errs: &mut Vec<LexBuildError>,
    ) -> LexInternalBuildResult<bool> {
        self.validate_start_state_name(span, name)?;
        if let Some(state) = self.start_states.iter().find(|state| state.name == name) {
            add_duplicate_occurrence(
                errs,
                LexErrorKind::DuplicateStartState,
                state.name_span,
                span,
            );
            Ok(false)
        } else {
            Ok(true)
        }
    }

    fn validate_start_state_name(&self, span: Span, name: &str) -> LexInternalBuildResult<()> {
        if !RE_START_STATE_NAME.is_match(name) {
            return Err(self.mk_error(LexErrorKind::InvalidStartStateName, span.start()));
        }
        Ok(())
    }

    fn parse_rules(
        &mut self,
        mut i: usize,
        errs: &mut Vec<LexBuildError>,
    ) -> LexInternalBuildResult<usize> {
        loop {
            i = self.parse_ws(i)?;
            if i == self.src.len() {
                break;
            }
            if self.lookahead_is("%%", i).is_some() {
                break;
            }
            i = self.parse_rule(i, errs)?;
        }
        Ok(i)
    }

    fn parse_rule(
        &mut self,
        i: usize,
        errs: &mut Vec<LexBuildError>,
    ) -> LexInternalBuildResult<usize> {
        let line_len = self.src[i..]
            .find(|c| c == '\n')
            .unwrap_or(self.src.len() - i);
        let line = self.src[i..i + line_len].trim_end();
        let rspace = match line.rfind(' ') {
            Some(j) => j,
            None => return Err(self.mk_error(LexErrorKind::MissingSpace, i)),
        };

        let name;
        let target_state;
        let orig_name = if line[rspace + 1..].starts_with('<') {
            match line[rspace + 1..].find('>') {
                Some(l) => {
                    let state = self.get_start_state_by_name(
                        i + rspace + 1,
                        &line[rspace + 2..rspace + 1 + l],
                    )?;
                    target_state = Some(state.id);
                    &line[rspace + 1 + l + 1..]
                }
                None => return Err(self.mk_error(LexErrorKind::InvalidStartState, rspace + i)),
            }
        } else {
            target_state = None;
            &line[rspace + 1..]
        };
        let name_span;
        let dupe = if orig_name == ";" || orig_name == r#""""# || orig_name == "''" {
            name = None;
            let pos = i + rspace + 1;
            name_span = Span::new(pos, pos);
            false
        } else {
            if orig_name.len() <= 2
                || !((orig_name.starts_with('\'') && orig_name.ends_with('\''))
                    || (orig_name.starts_with('\"') && orig_name.ends_with('"')))
            {
                return Err(self.mk_error(LexErrorKind::InvalidName, i + rspace + 1));
            }
            name = Some(orig_name[1..orig_name.len() - 1].to_string());
            name_span = Span::new(i + rspace + 2, i + rspace + orig_name.len());
            self.rules.iter().any(|r| {
                let dupe = r
                    .name
                    .as_ref()
                    .map_or(false, |n| n == name.as_ref().unwrap());
                if dupe {
                    add_duplicate_occurrence(
                        errs,
                        LexErrorKind::DuplicateName,
                        r.name_span,
                        name_span,
                    );
                }
                dupe
            })
        };

        if !dupe {
            let (start_states, re_str) = self.parse_start_states(i, line[..rspace].trim_end())?;
            let rules_len = self.rules.len();
            let tok_id = StorageT::try_from(rules_len)
                           .unwrap_or_else(|_| panic!("StorageT::try_from failed on {} (if StorageT is an unsigned integer type, this probably means that {} exceeds the type's maximum value)", rules_len, rules_len));

            let rule = Rule::new(
                Some(tok_id),
                name,
                name_span,
                re_str.to_string(),
                start_states,
                target_state,
            )
            .map_err(|_| self.mk_error(LexErrorKind::RegexError, i))?;
            self.rules.push(rule);
        }
        Ok(i + line_len)
    }

    fn parse_start_states<'a>(
        &self,
        off: usize,
        re_str: &'a str,
    ) -> LexInternalBuildResult<(Vec<usize>, std::borrow::Cow<'a, str>)> {
        if !re_str.starts_with('<') {
            /// This implements the 'Table: Escape Sequences in lex' from POSIX lex specification
            ///
            /// Most of the escape handling is left to regex, except this part:
            ///
            /// Escape: \c
            ///
            /// Description:
            /// A <backslash> character followed by any character not described in this table or in the table in
            /// XBD File Format Notation ( '\\', '\a', '\b', '\f' , '\n', '\r', '\t', '\v' ).
            ///
            /// Meaning: The character 'c', unchanged.
            fn unescape(re: Cow<str>) -> Cow<str> {
                // POSIX lex has two layers of escaping, there are escapes for the regular
                // expressions themselves and the escapes which get handled by lex directly.
                // We can find what the `regex` crate needs to be escaped with `is_meta_character`.
                //
                // We need to avoid sending Regex an escaped character which it does not consider
                // a meta_character. As that would fail to compile. While ensuring we retain
                // the escape sequences for the meta characters that it does require.
                //
                // '<' is interesting because when used at the beginning of a regex, intended to
                // be part of the regex, it needs to be escaped, otherwise lex will interpret it
                // as the beginning of a [`StartState`](StartState)
                //
                // If regex_syntax changes behavior here, it is highly likely that we should just
                // remove this assertion, and send regex `\<`. Instead of unescaping `\<` into `<`.
                // still it may be worthwhile to ensure that we notice such a change.
                debug_assert!(regex_syntax::is_meta_character('<').not());
                let re_str: &str = re.borrow();
                let mut re_chars = re_str.char_indices();

                // Look for an escape sequence which needs unescaping
                let mut cursor = loop {
                    if let Some((i, c)) = re_chars.next() {
                        if c == '\\' {
                            // Look at the next character and whether it is something we need to unescape
                            if let Some((j, c2)) = re_chars.next() {
                                let s = &re_str[j..];
                                if !(regex_syntax::is_meta_character(c2)
                                    || RE_LEX_ESC_LITERAL.is_match(s))
                                {
                                    break (Some((i, s, j, c2)));
                                }
                            }
                        }
                    } else {
                        break None;
                    }
                };

                if cursor.is_none() {
                    // There is nothing to unescape, return the original parameter
                    return re;
                }

                // At this point we have found something to unescape
                let mut unescaped = String::new();
                let mut last_pos = 0;

                'outer: while let Some((i, s, j, c)) = cursor {
                    if regex_syntax::is_meta_character(c) || RE_LEX_ESC_LITERAL.is_match(s) {
                        // For both meta characters and literals we want to push the entire substring
                        // up to and including the c match back into the string still escaped.
                        unescaped.push_str(&re_str[last_pos..j + c.len_utf8()]);
                        last_pos = j + c.len_utf8();
                    } else {
                        // Given '\c' in the original string, push 'c' to the new string.
                        unescaped.push_str(&re_str[last_pos..i]);
                        last_pos = j + c.len_utf8();
                        unescaped.push_str(&re_str[j..last_pos]);
                    }

                    // Continue looking for the next escape sequence in the original unmodified string.
                    loop {
                        if let Some((step1_pos, step1)) = re_chars.next() {
                            if step1 == '\\' {
                                cursor = re_chars.next().map(|(step2_pos, step2)| {
                                    (step1_pos, &re_str[step2_pos..], step2_pos, step2)
                                });
                                continue 'outer;
                            }
                        } else {
                            // Hit the end without finding another escape sequence. Copy over the trailing string.
                            unescaped.push_str(&re_str[last_pos..]);
                            break 'outer;
                        }
                    }
                }
                Cow::from(unescaped)
            }

            Ok((vec![], unescape(Cow::from(re_str))))
        } else {
            match re_str.find('>') {
                None => Err(self.mk_error(LexErrorKind::InvalidStartState, off)),
                Some(j) => {
                    let start_states = re_str[1..j]
                        .split(',')
                        .map(|s| s.trim())
                        .map(|s| self.get_start_state_by_name(off, s))
                        .map(|s| s.map(|ss| ss.id))
                        .collect::<LexInternalBuildResult<Vec<usize>>>()?;
                    Ok((start_states, Cow::from(&re_str[j + 1..])))
                }
            }
        }
    }

    fn get_start_state_by_name(
        &self,
        off: usize,
        state: &str,
    ) -> LexInternalBuildResult<&StartState> {
        self.start_states
            .iter()
            .find(|r| r.name == state)
            .ok_or_else(|| self.mk_error(LexErrorKind::UnknownStartState, off))
    }

    fn parse_ws(&mut self, i: usize) -> LexInternalBuildResult<usize> {
        let mut j = i;
        for c in self.src[i..].chars() {
            match c {
                ' ' | '\t' | '\n' | '\r' => (),
                _ => break,
            }
            j += c.len_utf8();
        }
        Ok(j)
    }

    fn lookahead_is(&self, s: &'static str, i: usize) -> Option<usize> {
        if self.src[i..].starts_with(s) {
            Some(i + s.len())
        } else {
            None
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::{
        lexer::{LRNonStreamingLexerDef, LexerDef},
        DefaultLexeme,
    };
    use std::fmt::Write as _;

    macro_rules! incorrect_errs {
        ($src:ident, $errs:expr) => {{
            for e in $errs {
                let mut line_cache = ::cfgrammar::newlinecache::NewlineCache::new();
                line_cache.feed(&$src);
                if let Some((line, column)) = line_cache
                    .byte_to_line_num_and_col_num(&$src, e.spans().next().unwrap().start())
                {
                    panic!(
                        "Incorrect error returned {} at line {line} column {column}",
                        e
                    )
                } else {
                    panic!("{}", e)
                }
            }
        }};
    }

    macro_rules! line_col {
        ($src:ident, $span: expr) => {{
            let mut line_cache = ::cfgrammar::newlinecache::NewlineCache::new();
            line_cache.feed(&$src);
            line_cache
                .byte_to_line_num_and_col_num(&$src, $span.start())
                .unwrap()
        }};
    }

    fn line_of_offset(s: &str, off: usize) -> usize {
        s[..off].lines().count()
    }

    trait ErrorsHelper {
        fn expect_error_at_line(self, src: &str, kind: LexErrorKind, line: usize);
        fn expect_error_at_line_col(self, src: &str, kind: LexErrorKind, line: usize, col: usize);
        fn expect_error_at_lines_cols(
            self,
            src: &str,
            kind: LexErrorKind,
            lines_cols: &mut dyn Iterator<Item = (usize, usize)>,
        );
        fn expect_multiple_errors(
            self,
            src: &str,
            expected: &mut dyn Iterator<Item = (LexErrorKind, Vec<(usize, usize)>)>,
        );
    }

    impl ErrorsHelper for Result<LRNonStreamingLexerDef<DefaultLexeme<u8>, u8>, Vec<LexBuildError>> {
        fn expect_error_at_line(self, src: &str, kind: LexErrorKind, line: usize) {
            match self.as_ref().map_err(Vec::as_slice) {
                Ok(_) => panic!("Parsed ok while expecting error"),
                Err([e])
                    if e.kind == kind
                        && line_of_offset(src, e.spans().next().unwrap().start()) == line
                        && e.spans.len() == 1 => {}
                Err(e) => incorrect_errs!(src, e),
            }
        }

        fn expect_error_at_line_col(self, src: &str, kind: LexErrorKind, line: usize, col: usize) {
            self.expect_error_at_lines_cols(src, kind, &mut std::iter::once((line, col)))
        }

        fn expect_error_at_lines_cols(
            self,
            src: &str,
            kind: LexErrorKind,
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

        fn expect_multiple_errors(
            self,
            src: &str,
            expected: &mut dyn Iterator<Item = (LexErrorKind, Vec<(usize, usize)>)>,
        ) {
            match self {
                Ok(_) => panic!("Parsed ok while expecting error"),
                Err(errs)
                    if errs
                        .iter()
                        .map(|e| {
                            (
                                e.kind.clone(),
                                e.spans()
                                    .map(|span| line_col!(src, span))
                                    .collect::<Vec<_>>(),
                            )
                        })
                        .eq(expected) => {}
                Err(errs) => incorrect_errs!(src, errs),
            }
        }
    }

    #[test]
    fn test_nooptions() {
        let src = "
%option nounput
        "
        .to_string();
        assert!(LRNonStreamingLexerDef::<DefaultLexeme<u8>, u8>::from_str(&src).is_err());
    }

    #[test]
    fn test_minimum() {
        let src = "%%".to_string();
        assert!(LRNonStreamingLexerDef::<DefaultLexeme<u8>, u8>::from_str(&src).is_ok());
    }

    #[test]
    fn test_rules() {
        let src = "%%
[0-9]+ 'int'
[a-zA-Z]+ 'id'
\\+ '+'
"
        .to_string();
        let ast = LRNonStreamingLexerDef::<DefaultLexeme<u8>, u8>::from_str(&src).unwrap();
        let intrule = ast.get_rule_by_name("int").unwrap();
        assert_eq!("int", intrule.name.as_ref().unwrap());
        assert_eq!("[0-9]+", intrule.re_str);
        let idrule = ast.get_rule_by_name("id").unwrap();
        assert_eq!("id", idrule.name.as_ref().unwrap());
        assert_eq!("[a-zA-Z]+", idrule.re_str);
        let plusrule = ast.get_rule_by_name("+").unwrap();
        assert_eq!("+", plusrule.name.as_ref().unwrap());
        assert_eq!("\\+", plusrule.re_str);
    }

    #[test]
    fn test_no_name() {
        let src = "%%
[0-9]+ ;
"
        .to_string();
        let ast = LRNonStreamingLexerDef::<DefaultLexeme<u8>, u8>::from_str(&src).unwrap();
        let intrule = ast.get_rule(0).unwrap();
        assert!(intrule.name.is_none());
        assert_eq!("[0-9]+", intrule.re_str);
    }

    #[test]
    fn test_broken_rule() {
        let src = "%%
[0-9]
'int'"
            .to_string();
        assert!(LRNonStreamingLexerDef::<DefaultLexeme<u8>, u8>::from_str(&src).is_err());
        LRNonStreamingLexerDef::<DefaultLexeme<u8>, u8>::from_str(&src).expect_error_at_line_col(
            &src,
            LexErrorKind::MissingSpace,
            2,
            1,
        )
    }

    #[test]
    fn test_broken_rule2() {
        let src = "%%
[0-9] "
            .to_string();
        assert!(LRNonStreamingLexerDef::<DefaultLexeme<u8>, u8>::from_str(&src).is_err());
        LRNonStreamingLexerDef::<DefaultLexeme<u8>, u8>::from_str(&src).expect_error_at_line_col(
            &src,
            LexErrorKind::MissingSpace,
            2,
            1,
        )
    }

    #[test]
    fn test_broken_rule3() {
        let src = "%%
[0-9] int"
            .to_string();
        assert!(LRNonStreamingLexerDef::<DefaultLexeme<u8>, u8>::from_str(&src).is_err());
        LRNonStreamingLexerDef::<DefaultLexeme<u8>, u8>::from_str(&src).expect_error_at_line_col(
            &src,
            LexErrorKind::InvalidName,
            2,
            7,
        )
    }

    #[test]
    fn test_broken_rule4() {
        let src = "%%
[0-9] 'int"
            .to_string();
        assert!(LRNonStreamingLexerDef::<DefaultLexeme<u8>, u8>::from_str(&src).is_err());
        LRNonStreamingLexerDef::<DefaultLexeme<u8>, u8>::from_str(&src).expect_error_at_line_col(
            &src,
            LexErrorKind::InvalidName,
            2,
            7,
        )
    }

    #[test]
    fn test_broken_rule_names_with_spaces() {
        let srcs = [r#"a ""#, "a '", r#"a '""#, r#"a "'"#];
        for line_two in srcs {
            let src = format!("%%\n{line_two}");
            LRNonStreamingLexerDef::<DefaultLexeme<u8>, u8>::from_str(&src)
                .expect_error_at_line_col(&src, LexErrorKind::InvalidName, 2, 3);
        }

        let srcs = [
            r#"a " ""#,
            "a ' '",
            r#"a ' "'"#,
            r#"a " Name"#,
            r#"a " Name""#,
            "a ' Name",
            "a ' Name'",
            r#"a " '""#,
        ];

        for line_two in srcs {
            let src = format!("%%\n{line_two}");
            LRNonStreamingLexerDef::<DefaultLexeme<u8>, u8>::from_str(&src)
                .expect_error_at_line_col(&src, LexErrorKind::InvalidName, 2, 5);
        }
    }

    #[test]
    fn test_unusual_ok_rules() {
        // Unusual cases of valid regexes and names, that make splitting them tricky.
        let srcs = [
            r#"[ "] 'a'"#,
            r#"[ "] "a""#,
            r#"[ "] ;"#,
            r#"[ "] """#,
            r#"[ "] ''"#,
            r#"[ '] "a""#,
            r#"[ '] ;"#,
            r#"[ '] """#,
            "[ '] ''",
            "[ '] 'a'",
            "[ '] ;",
        ];
        for line_two in srcs {
            let src = format!("%%\n{line_two}");
            assert!(LRNonStreamingLexerDef::<DefaultLexeme<u8>, u8>::from_str(&src).is_ok());
        }
    }

    #[test]
    fn test_duplicate_rule() {
        let src = "%%
[0-9] 'int'
[0-9] 'int'
[0-9] 'int'"
            .to_string();
        LRNonStreamingLexerDef::<DefaultLexeme<u8>, u8>::from_str(&src).expect_error_at_lines_cols(
            &src,
            LexErrorKind::DuplicateName,
            &mut [(2, 8), (3, 8), (4, 8)].into_iter(),
        )
    }

    #[test]
    fn multiple_duplicate_rules() {
        let src = "%%
[0-9] 'int'
[A-Z] 'ALPHA'
[0-9] 'int'
[A-Z] 'ALPHA'
[0-9] 'int'
[A-Z] 'ALPHA'"
            .to_string();
        LRNonStreamingLexerDef::<DefaultLexeme<u8>, u8>::from_str(&src).expect_multiple_errors(
            &src,
            &mut [
                (LexErrorKind::DuplicateName, vec![(2, 8), (4, 8), (6, 8)]),
                (LexErrorKind::DuplicateName, vec![(3, 8), (5, 8), (7, 8)]),
            ]
            .into_iter(),
        )
    }

    #[test]
    fn start_state_declaration_containing_underscore() {
        let src = "%start_state KNOWN
%%
<KNOWN>. 'known'"
            .to_string();
        LRNonStreamingLexerDef::<DefaultLexeme<u8>, u8>::from_str(&src).expect_error_at_line_col(
            &src,
            LexErrorKind::UnknownDeclaration,
            1,
            1,
        )
    }

    #[test]
    fn start_state_declaration_missing() {
        let src = "%s
%%
<KNOWN>. 'known'"
            .to_string();
        LRNonStreamingLexerDef::<DefaultLexeme<u8>, u8>::from_str(&src).expect_error_at_line_col(
            &src,
            LexErrorKind::UnknownDeclaration,
            1,
            1,
        )
    }

    #[test]
    fn start_state_declaration_empty() {
        let src = "%s
%%
<KNOWN>. 'known'"
            .to_string();
        LRNonStreamingLexerDef::<DefaultLexeme<u8>, u8>::from_str(&src).expect_error_at_line_col(
            &src,
            LexErrorKind::UnknownDeclaration,
            1,
            1,
        )
    }

    #[test]
    fn start_state_name_alphanumeric_starting_number() {
        let src = "%s 1KNOWN
%%
<KNOWN>. 'known'"
            .to_string();
        LRNonStreamingLexerDef::<DefaultLexeme<u8>, u8>::from_str(&src).expect_error_at_line_col(
            &src,
            LexErrorKind::InvalidStartStateName,
            1,
            4,
        )
    }

    #[test]
    fn start_state_name_pure_numeric() {
        let src = "%s 123
%%
<123>. 'known'"
            .to_string();
        LRNonStreamingLexerDef::<DefaultLexeme<u8>, u8>::from_str(&src).expect_error_at_line_col(
            &src,
            LexErrorKind::InvalidStartStateName,
            1,
            4,
        )
    }

    #[test]
    fn rule_with_numeric_start_state() {
        let src = "%%
<1>. 'known'"
            .to_string();
        LRNonStreamingLexerDef::<DefaultLexeme<u8>, u8>::from_str(&src).expect_error_at_line_col(
            &src,
            LexErrorKind::UnknownStartState,
            2,
            1,
        )
    }

    #[test]
    fn transition_to_numeric_start_state() {
        let src = "%%
. <1>'known'"
            .to_string();
        LRNonStreamingLexerDef::<DefaultLexeme<u8>, u8>::from_str(&src).expect_error_at_line_col(
            &src,
            LexErrorKind::UnknownStartState,
            2,
            3,
        )
    }

    #[test]
    fn known_current_start_state() {
        let src = "%s KNOWN
%%
<KNOWN>. 'known'"
            .to_string();
        let ast = LRNonStreamingLexerDef::<DefaultLexeme<u8>, u8>::from_str(&src).unwrap();
        let intrule = ast.get_rule(0).unwrap();
        assert_eq!("known", intrule.name.as_ref().unwrap());
        assert_eq!(".", intrule.re_str);
        assert!(intrule.target_state.is_none());
        assert_eq!(1, intrule.start_states.len());
        assert_eq!(1, *intrule.start_states.get(0).unwrap());
    }

    #[test]
    fn unknown_current_start_state() {
        let src = "%%
<UNKNOWN>. 'unknown'"
            .to_string();
        LRNonStreamingLexerDef::<DefaultLexeme<u8>, u8>::from_str(&src).expect_error_at_line_col(
            &src,
            LexErrorKind::UnknownStartState,
            2,
            1,
        )
    }

    #[test]
    fn known_target_start_state() {
        let src = "%s KNOWN
%%
. <KNOWN>'known'"
            .to_string();
        let ast = LRNonStreamingLexerDef::<DefaultLexeme<u8>, u8>::from_str(&src).unwrap();
        let intrule = ast.get_rule(0).unwrap();
        assert_eq!("known", intrule.name.as_ref().unwrap());
        assert_eq!(".", intrule.re_str);
        assert_eq!(1, intrule.target_state.unwrap());
        assert_eq!(0, intrule.start_states.len());
    }

    #[test]
    fn unknown_target_start_state() {
        let src = "%%
. <UNKNOWN>'unknown'"
            .to_string();
        LRNonStreamingLexerDef::<DefaultLexeme<u8>, u8>::from_str(&src).expect_error_at_line_col(
            &src,
            LexErrorKind::UnknownStartState,
            2,
            3,
        )
    }

    #[test]
    fn unterminated_required_start_state() {
        let src = "%%
<test. 'TEST'"
            .to_string();
        LRNonStreamingLexerDef::<DefaultLexeme<u8>, u8>::from_str(&src).expect_error_at_line_col(
            &src,
            LexErrorKind::InvalidStartState,
            2,
            1,
        )
    }

    #[test]
    fn unterminated_transition_start_state() {
        let src = "%%
. <test'TEST'"
            .to_string();
        LRNonStreamingLexerDef::<DefaultLexeme<u8>, u8>::from_str(&src).expect_error_at_line_col(
            &src,
            LexErrorKind::InvalidStartState,
            2,
            2,
        )
    }

    #[test]
    fn invalid_start_state_definition() {
        let src = "%x 1test
%%
. 'TEST'"
            .to_string();
        LRNonStreamingLexerDef::<DefaultLexeme<u8>, u8>::from_str(&src).expect_error_at_line_col(
            &src,
            LexErrorKind::InvalidStartStateName,
            1,
            4,
        )
    }

    #[test]
    fn long_form_start_state_definition() {
        let src = "%START test
%%
. 'TEST'"
            .to_string();
        let ast = LRNonStreamingLexerDef::<DefaultLexeme<u8>, u8>::from_str(&src).unwrap();
        // Expect two start states - INITIAL + test
        assert_eq!(2, ast.iter_start_states().count());
        assert!(ast
            .iter_start_states()
            .any(|ss| !ss.exclusive && ss.name == INITIAL_START_STATE_NAME));
        assert!(ast
            .iter_start_states()
            .any(|ss| !ss.exclusive && ss.name == "test"));
    }

    #[test]
    fn short_form_start_state_definition() {
        let src = "%S test
%%
. 'TEST'"
            .to_string();
        let ast = LRNonStreamingLexerDef::<DefaultLexeme<u8>, u8>::from_str(&src).unwrap();
        // Expect two start states - INITIAL + test
        assert_eq!(2, ast.iter_start_states().count());
        assert!(ast
            .iter_start_states()
            .any(|ss| !ss.exclusive && ss.name == INITIAL_START_STATE_NAME));
        assert!(ast
            .iter_start_states()
            .any(|ss| !ss.exclusive && ss.name == "test"));
    }

    #[test]
    fn exclusive_start_state_definition() {
        let src = "%x test
%%
. 'TEST'"
            .to_string();
        let ast = LRNonStreamingLexerDef::<DefaultLexeme<u8>, u8>::from_str(&src).unwrap();
        // Expect two start states - INITIAL + test
        assert_eq!(2, ast.iter_start_states().count());
        assert!(ast
            .iter_start_states()
            .any(|ss| !ss.exclusive && ss.name == INITIAL_START_STATE_NAME));
        assert!(ast
            .iter_start_states()
            .any(|ss| ss.exclusive && ss.name == "test"));
    }

    #[test]
    fn duplicate_start_state_definition() {
        let src = "%s test
%s test
%%
. 'TEST'"
            .to_string();
        LRNonStreamingLexerDef::<DefaultLexeme<u8>, u8>::from_str(&src).expect_error_at_lines_cols(
            &src,
            LexErrorKind::DuplicateStartState,
            &mut [(1, 4), (2, 4)].into_iter(),
        )
    }

    #[test]
    fn duplicate_start_state_definition_one_line() {
        let src = "%s test test1 test
        %%
        . 'TEST'"
            .to_string();
        LRNonStreamingLexerDef::<DefaultLexeme<u8>, u8>::from_str(&src).expect_error_at_lines_cols(
            &src,
            LexErrorKind::DuplicateStartState,
            &mut [(1, 4), (1, 15)].into_iter(),
        )
    }

    #[test]
    fn multiple_duplicate_start_state_definition() {
        let src = "%s test test2
%s test test2
%%
. 'TEST'"
            .to_string();
        LRNonStreamingLexerDef::<DefaultLexeme<u8>, u8>::from_str(&src).expect_multiple_errors(
            &src,
            &mut [
                (LexErrorKind::DuplicateStartState, vec![(1, 4), (2, 4)]),
                (LexErrorKind::DuplicateStartState, vec![(1, 9), (2, 9)]),
            ]
            .into_iter(),
        )
    }

    #[test]
    fn start_state_operators_begin_of_regex() {
        // As a sanity check, since we rely on this for proper escaping behavior
        // This is guaranteed not to change without a semver bump by regex_syntax.
        assert!(regex_syntax::is_meta_character('<').not());
        // Test escaping '<' and '>' start state operators, as the initial characters of a regex.
        let src = r#"
%%
\> 'gt'
\< 'lt'
a< 'alt'
a> 'agt'
e\<\< 'elt'
e\>\> 'egt'
\∀ 'forall'
\∀\∀ 'forall2'
\∀∀∀∀\∀ 'forall3'
∀∀∀\∀∀ 'forall4'
\[\] 'box'
a\[\] 'abox'
a\[\]a 'aboxa'
\x2a 'hex'
\052 'octal'
\n* 'newline'
\a* 'alert'
\\* 'backslash'
\\\\* 'backslash2'
[\\\na]* 'backslash_newline_a'
[\\<a]* 'backslash_angle_a'
[\\\<a]* 'backslash_angle_a2'
\u2200 'forall5'
\U00002200 'forall6'
[\nabcdefg\t] 'bookend'
[\nabc\adefg\t] 'bookend2'
[\nabc\<defg\t] 'bookend3'
[\tabcdefg\<] 'bookend4'
[\<abcdefg\t] 'bookend5'
"#
        .to_string();
        let ast = LRNonStreamingLexerDef::<DefaultLexeme<u8>, u8>::from_str(&src).unwrap();
        let mut rule = ast.get_rule_by_name("gt").unwrap();
        assert_eq!("gt", rule.name.as_ref().unwrap());
        assert_eq!(">", rule.re_str);
        rule = ast.get_rule_by_name("lt").unwrap();
        assert_eq!("lt", rule.name.as_ref().unwrap());
        assert_eq!("<", rule.re_str);
        rule = ast.get_rule_by_name("alt").unwrap();
        assert_eq!("alt", rule.name.as_ref().unwrap());
        assert_eq!("a<", rule.re_str);
        rule = ast.get_rule_by_name("agt").unwrap();
        assert_eq!("agt", rule.name.as_ref().unwrap());
        assert_eq!("a>", rule.re_str);
        rule = ast.get_rule_by_name("elt").unwrap();
        assert_eq!("elt", rule.name.as_ref().unwrap());
        assert_eq!("e<<", rule.re_str);
        rule = ast.get_rule_by_name("egt").unwrap();
        assert_eq!("egt", rule.name.as_ref().unwrap());
        assert_eq!("e>>", rule.re_str);
        rule = ast.get_rule_by_name("forall").unwrap();
        assert_eq!("forall", rule.name.as_ref().unwrap());
        assert_eq!("∀", rule.re_str);
        rule = ast.get_rule_by_name("forall2").unwrap();
        assert_eq!("forall2", rule.name.as_ref().unwrap());
        assert_eq!("∀∀", rule.re_str);
        rule = ast.get_rule_by_name("forall3").unwrap();
        assert_eq!("forall3", rule.name.as_ref().unwrap());
        assert_eq!("∀∀∀∀∀", rule.re_str);
        rule = ast.get_rule_by_name("forall4").unwrap();
        assert_eq!("forall4", rule.name.as_ref().unwrap());
        assert_eq!("∀∀∀∀∀", rule.re_str);
        rule = ast.get_rule_by_name("box").unwrap();
        assert_eq!("box", rule.name.as_ref().unwrap());
        assert_eq!(r"\[\]", rule.re_str);
        rule = ast.get_rule_by_name("abox").unwrap();
        assert_eq!("abox", rule.name.as_ref().unwrap());
        assert_eq!(r"a\[\]", rule.re_str);
        rule = ast.get_rule_by_name("aboxa").unwrap();
        assert_eq!("aboxa", rule.name.as_ref().unwrap());
        assert_eq!(r"a\[\]a", rule.re_str);
        rule = ast.get_rule_by_name("hex").unwrap();
        assert_eq!("hex", rule.name.as_ref().unwrap());
        assert_eq!(r"\x2a", rule.re_str);
        rule = ast.get_rule_by_name("octal").unwrap();
        assert_eq!("octal", rule.name.as_ref().unwrap());
        assert_eq!(r"\052", rule.re_str);
        rule = ast.get_rule_by_name("newline").unwrap();
        assert_eq!("newline", rule.name.as_ref().unwrap());
        assert_eq!(r"\n*", rule.re_str);
        rule = ast.get_rule_by_name("alert").unwrap();
        assert_eq!("alert", rule.name.as_ref().unwrap());
        assert_eq!(r"\a*", rule.re_str);
        rule = ast.get_rule_by_name("backslash").unwrap();
        assert_eq!("backslash", rule.name.as_ref().unwrap());
        assert_eq!(r"\\*", rule.re_str);
        rule = ast.get_rule_by_name("backslash2").unwrap();
        assert_eq!("backslash2", rule.name.as_ref().unwrap());
        assert_eq!(r"\\\\*", rule.re_str);
        rule = ast.get_rule_by_name("backslash_newline_a").unwrap();
        assert_eq!("backslash_newline_a", rule.name.as_ref().unwrap());
        assert_eq!(r"[\\\na]*", rule.re_str);
        rule = ast.get_rule_by_name("backslash_angle_a").unwrap();
        assert_eq!("backslash_angle_a", rule.name.as_ref().unwrap());
        assert_eq!(r"[\\<a]*", rule.re_str);
        rule = ast.get_rule_by_name("forall5").unwrap();
        assert_eq!("forall5", rule.name.as_ref().unwrap());
        assert_eq!(r"\u2200", rule.re_str);
        rule = ast.get_rule_by_name("forall6").unwrap();
        assert_eq!("forall6", rule.name.as_ref().unwrap());
        assert_eq!(r"\U00002200", rule.re_str);
        rule = ast.get_rule_by_name("bookend").unwrap();
        assert_eq!("bookend", rule.name.as_ref().unwrap());
        assert_eq!(r"[\nabcdefg\t]", rule.re_str);
        rule = ast.get_rule_by_name("bookend2").unwrap();
        assert_eq!("bookend2", rule.name.as_ref().unwrap());
        assert_eq!(r"[\nabc\adefg\t]", rule.re_str);
        rule = ast.get_rule_by_name("bookend3").unwrap();
        assert_eq!("bookend3", rule.name.as_ref().unwrap());
        assert_eq!(r"[\nabc<defg\t]", rule.re_str);
        rule = ast.get_rule_by_name("bookend4").unwrap();
        assert_eq!("bookend4", rule.name.as_ref().unwrap());
        assert_eq!(r"[\tabcdefg<]", rule.re_str);
        rule = ast.get_rule_by_name("bookend5").unwrap();
        assert_eq!("bookend5", rule.name.as_ref().unwrap());
        assert_eq!(r"[<abcdefg\t]", rule.re_str);
    }

    #[test]
    fn inconsistent_duplicate_start_state_definition() {
        let src = "%x test
%s test
%%
. 'TEST'"
            .to_string();
        LRNonStreamingLexerDef::<DefaultLexeme<u8>, u8>::from_str(&src).expect_error_at_lines_cols(
            &src,
            LexErrorKind::DuplicateStartState,
            &mut [(1, 4), (2, 4)].into_iter(),
        )
    }

    #[test]
    fn invalid_required_start_state() {
        let src = "%%
<1test>. 'TEST'"
            .to_string();
        LRNonStreamingLexerDef::<DefaultLexeme<u8>, u8>::from_str(&src).expect_error_at_line_col(
            &src,
            LexErrorKind::UnknownStartState,
            2,
            1,
        )
    }

    #[test]
    fn invalid_transition_start_state() {
        let src = "%%
. <1test>'TEST'"
            .to_string();
        LRNonStreamingLexerDef::<DefaultLexeme<u8>, u8>::from_str(&src).expect_error_at_line_col(
            &src,
            LexErrorKind::UnknownStartState,
            2,
            3,
        )
    }

    #[test]
    #[should_panic]
    fn exceed_tok_id_capacity() {
        let mut src = "%%
"
        .to_string();
        for i in 0..257 {
            writeln!(src, "x 'x{}'\n", i).ok();
        }
        LRNonStreamingLexerDef::<DefaultLexeme<u8>, u8>::from_str(&src).ok();
    }
}
