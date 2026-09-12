use crate::{
    Location, Span, Spanned,
    markmap::{Entry, MarkMap},
    yacc::{
        YaccGrammarError, YaccGrammarErrorKind, YaccKind, YaccOriginalActionKind, parser::SpansKind,
    },
};
use regex::{Regex, RegexBuilder};
use std::{collections::HashMap, error::Error, fmt, sync::LazyLock};

/// An error regarding the `%grmtools` header section.
///
/// It could be any of:
///
/// * An error during parsing the section.
/// * An error resulting from a value in the section having an invalid value.
#[derive(Debug, Clone)]
#[doc(hidden)]
pub struct HeaderError<T> {
    pub kind: HeaderErrorKind,
    pub locations: Vec<T>,
}

impl<T: fmt::Debug> Error for HeaderError<T> {}
impl<T> fmt::Display for HeaderError<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.kind)
    }
}

impl From<HeaderError<Span>> for YaccGrammarError {
    fn from(e: HeaderError<Span>) -> YaccGrammarError {
        YaccGrammarError {
            kind: YaccGrammarErrorKind::Header(e.kind, e.spanskind()),
            spans: e.locations,
        }
    }
}

impl Spanned for HeaderError<Span> {
    fn spans(&self) -> &[Span] {
        self.locations.as_slice()
    }
    fn spanskind(&self) -> SpansKind {
        self.spanskind()
    }
}

// This is essentially a tuple that needs a newtype so we can implement `From` for it.
// Thus we aren't worried about it being `pub`.
#[derive(Debug, PartialEq, Clone)]
#[doc(hidden)]
pub struct HeaderValue<T>(pub T, pub Value<T>);

impl From<HeaderValue<Span>> for HeaderValue<Location> {
    fn from(hv: HeaderValue<Span>) -> HeaderValue<Location> {
        HeaderValue(hv.0.into(), hv.1.into())
    }
}

#[derive(Debug, Eq, PartialEq, Copy, Clone)]
#[non_exhaustive]
#[doc(hidden)]
pub enum HeaderErrorKind {
    MissingGrmtoolsSection,
    IllegalName,
    ExpectedToken(char),
    UnexpectedToken(char, &'static str),
    DuplicateEntry,
    InvalidEntry(&'static str),
    ConversionError(&'static str, &'static str),
}

impl fmt::Display for HeaderErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let s = match self {
            HeaderErrorKind::MissingGrmtoolsSection => "Missing %grmtools section",
            HeaderErrorKind::IllegalName => "Illegal name",
            HeaderErrorKind::ExpectedToken(c) => &format!("Expected token: '{}'", c),
            HeaderErrorKind::UnexpectedToken(c, hint) => {
                &format!("Unxpected token: '{}', {} ", c, hint)
            }
            HeaderErrorKind::InvalidEntry(s) => &format!("Invalid entry: '{}'", s),
            HeaderErrorKind::DuplicateEntry => "Duplicate Entry",
            HeaderErrorKind::ConversionError(t, err_str) => {
                &format!("Converting header value to type '{}': {}", t, err_str)
            }
        };
        write!(f, "{}", s)
    }
}

/// Parser for the `%grmtools` section
#[doc(hidden)]
pub struct GrmtoolsSectionParser<'input> {
    src: &'input str,
    required: bool,
}

/// The value contained within a `Header`
///
/// To be useful across diverse crates this types fields are largely limited to types derived from `core::` types.
/// like booleans, numeric types, and string values. The exception to this is `Namespaced` which still must
///  be able to be marshalled through a string value.
///
/// The generic parameter `T` indicates the source of the value, for values read from a `%grmtools` section
/// this should be a `Span`. For other values which stem from command line arguments, or a programmatic interface
/// this should be a `Location`.
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum Value<T> {
    String(String, T),
    Num(u64, T),
    Bool(bool, T),
    Array(Vec<Value<T>>, T),
    /// A Rust like value, with an optional type namespace.
    /// For instance, you can omit the optional prefix `YaccKind::`
    /// specifying `YaccKind::Grmtools` or `Grmtools`.
    ///
    /// Further examples of `Namespaced` values:
    /// * YaccKind::Original(UserAction) or YaccKind::Original(YaccOriginalActionKind::UserAction)
    /// * Original(UserAction) or Original(YaccOriginalActionKind::UserAction)
    Namespaced(String, T),
}

impl From<Value<Span>> for Value<Location> {
    fn from(it: Value<Span>) -> Value<Location> {
        use Value as GV;
        match it {
            GV::String(v, span) => GV::String(v, Location::Span(span)),
            GV::Num(v, span) => GV::Num(v, Location::Span(span)),
            GV::Bool(v, span) => GV::Bool(v, Location::Span(span)),
            GV::Array(mut v, span) => GV::Array(
                v.drain(..).map(|val| val.into()).collect::<Vec<_>>(),
                Location::Span(span),
            ),
            GV::Namespaced(v, span) => GV::Namespaced(v, Location::Span(span)),
        }
    }
}

impl<T> HeaderError<T> {
    /// Returns the [SpansKind] associated with this error.
    pub fn spanskind(&self) -> SpansKind {
        match self.kind {
            HeaderErrorKind::DuplicateEntry => SpansKind::DuplicationError,
            _ => SpansKind::Error,
        }
    }
}

static RE_LEADING_WS: LazyLock<Regex> =
    LazyLock::new(|| Regex::new(r"^[\p{Pattern_White_Space}]*").unwrap());
static RE_NAME: LazyLock<Regex> = LazyLock::new(|| {
    RegexBuilder::new(r"^[A-Z][A-Z_\.]*")
        .case_insensitive(true)
        .build()
        .unwrap()
});
#[doc(hidden)]
pub static RE_CRATE_DOT: LazyLock<Regex> = LazyLock::new(|| {
    RegexBuilder::new(r"^[A-Z][A-Z_]*\.")
        .case_insensitive(true)
        .build()
        .unwrap()
});
static RE_DIGITS: LazyLock<Regex> = LazyLock::new(|| Regex::new(r"^[0-9]+").unwrap());
static RE_STRING: LazyLock<Regex> = LazyLock::new(|| Regex::new(r#"^\"(\\.|[^"\\])*\""#).unwrap());
#[doc(hidden)]
pub static CRATE_KEY_MAP: LazyLock<HashMap<&'static str, &'static str>> = LazyLock::new(|| {
    let mut map = HashMap::new();
    let cfgrammar = ["yacckind"];
    let lrpar = ["recoverer", "test_files", "serialisation_format"];

    let lrlex = ["lexerkind", "allow_wholeline_comments", "posix_escapes"];
    let regex = [
        "case_insensitive",
        "dot_matches_new_line",
        "multi_line",
        "octal",
        "swap_greed",
        "ignore_whitespace",
        "unicode",
        "size_limit",
        "dfa_size_limit",
        "nest_limit",
    ];
    for s in cfgrammar {
        map.insert(s, "cfgrammar");
    }
    for s in lrpar {
        map.insert(s, "lrpar");
    }
    for s in lrlex {
        map.insert(s, "lrlex");
    }
    for s in regex {
        map.insert(s, "regex");
    }
    map
});

const MAGIC: &str = "%grmtools";

fn add_duplicate_occurrence<T: Eq + PartialEq + Clone>(
    errs: &mut Vec<HeaderError<T>>,
    kind: HeaderErrorKind,
    orig_loc: T,
    dup_loc: T,
) {
    if !errs.iter_mut().any(|e| {
        if e.kind == kind && e.locations[0] == orig_loc {
            e.locations.push(dup_loc.clone());
            true
        } else {
            false
        }
    }) {
        errs.push(HeaderError {
            kind,
            locations: vec![orig_loc, dup_loc],
        });
    }
}

impl<'input> GrmtoolsSectionParser<'input> {
    fn parse_value(&'_ self, mut i: usize) -> Result<(Value<Span>, usize), HeaderError<Span>> {
        i = self.parse_ws(i);
        match RE_DIGITS.find(&self.src[i..]) {
            Some(m) => {
                let num_span = Span::new(i + m.start(), i + m.end());
                let num_str = &self.src[num_span.start()..num_span.end()];
                // If the above regex matches we expect this to succeed.
                let num = str::parse::<u64>(num_str).unwrap();
                let val = Value::Num(num, num_span);
                i = self.parse_ws(num_span.end());
                Ok((val, i))
            }
            None => match RE_STRING.find(&self.src[i..]) {
                Some(m) => {
                    let end = i + m.end();
                    // Trim the leading and trailing quotes.
                    let str_span = Span::new(i + m.start() + 1, end - 1);
                    let str = &self.src[str_span.start()..str_span.end()];
                    let setting = Value::String(str.to_string(), str_span);
                    // After the trailing quotes.
                    i = self.parse_ws(end);
                    Ok((setting, i))
                }
                None => {
                    if let Some(mut j) = self.lookahead_is("[", i) {
                        let mut vals = Vec::new();
                        loop {
                            j = self.parse_ws(j);
                            if let Some(end_pos) = self.lookahead_is("]", j) {
                                return Ok((Value::Array(vals, Span::new(i, end_pos)), end_pos));
                            }
                            if let Ok((val, k)) = self.parse_value(j) {
                                vals.push(val);
                                j = self.parse_ws(k);
                            }
                            if let Some(k) = self.lookahead_is(",", j) {
                                j = k
                            }
                        }
                    } else {
                        let ((path_val, path_span), j) = self.parse_namespaced(i)?;
                        i = self.parse_ws(j);
                        if let Some(j) = self.lookahead_is("(", i) {
                            let ((arg, _), j) = self.parse_namespaced(j)?;
                            i = self.parse_ws(j);
                            if let Some(j) = self.lookahead_is(")", i) {
                                i = self.parse_ws(j);
                                let span = Span::new(path_span.start(), j);
                                Ok(((Value::Namespaced(format!("{path_val}({arg})"), span)), i))
                            } else {
                                Err(HeaderError {
                                    kind: HeaderErrorKind::ExpectedToken(')'),
                                    locations: vec![Span::new(i, i)],
                                })
                            }
                        } else {
                            Ok((Value::Namespaced(path_val, path_span), i))
                        }
                    }
                }
            },
        }
    }

    pub fn parse_key_value(
        &'_ self,
        mut i: usize,
    ) -> Result<(String, Span, Value<Span>, usize), HeaderError<Span>> {
        if let Some(j) = self.lookahead_is("!", i) {
            let (flag_name, k) = self.parse_name(j)?;
            Ok((
                flag_name,
                Span::new(j, k),
                Value::Bool(false, Span::new(i, k)),
                self.parse_ws(k),
            ))
        } else {
            let (key_name, j) = self.parse_name(i)?;
            let key_span = Span::new(i, j);
            i = self.parse_ws(j);
            if let Some(j) = self.lookahead_is(":", i) {
                let (val, j) = self.parse_value(j)?;
                Ok((key_name, key_span, val, j))
            } else {
                Ok((key_name, key_span, Value::Bool(true, key_span), i))
            }
        }
    }

    fn parse_namespaced(&self, mut i: usize) -> Result<((String, Span), usize), HeaderError<Span>> {
        // Either a name alone, or a type::name.
        let (name, j) = self.parse_name(i)?;
        let name_span = Span::new(i, j);
        i = self.parse_ws(j);
        if let Some(j) = self.lookahead_is("::", i) {
            i = self.parse_ws(j);
            let (member_val, j) = self.parse_name(i)?;
            let member_val_span = Span::new(i, j);
            i = self.parse_ws(j);
            let span = Span::new(name_span.start(), member_val_span.end());
            Ok(((format!("{name}::{member_val}"), span), i))
        } else {
            Ok(((name, name_span), i))
        }
    }

    /// Parses any `%grmtools` section at the beginning of `src`.
    /// If `required` is true, the parse function will
    /// return an error if the `%grmtools` section is
    /// missing.
    ///
    /// If required is set and the section is empty, no error will be
    /// produced. If a caller requires a value they should
    /// produce an error that specifies the required value.
    ///
    pub fn new(src: &'input str, required: bool) -> Self {
        Self { src, required }
    }

    #[allow(clippy::type_complexity)]
    pub fn parse(&'_ self) -> Result<(Header<Span>, usize), Vec<HeaderError<Span>>> {
        let mut errs = Vec::new();
        if let Some(mut i) = self.lookahead_is(MAGIC, self.parse_ws(0)) {
            let mut ret = Header::new();
            i = self.parse_ws(i);
            let section_start_pos = i;
            if let Some(j) = self.lookahead_is("{", i) {
                i = self.parse_ws(j);
                while self.lookahead_is("}", i).is_none() && i < self.src.len() {
                    let (key, key_loc, val, j) = match self.parse_key_value(i) {
                        Ok((key, key_loc, val, pos)) => {
                            let key = if !RE_CRATE_DOT.is_match(&key) {
                                if let Some(crate_name) = CRATE_KEY_MAP.get(key.as_str()) {
                                    format!("{crate_name}.{key}")
                                } else {
                                    key
                                }
                            } else {
                                key
                            };
                            (key, key_loc, val, pos)
                        }
                        Err(e) => {
                            errs.push(e);
                            return Err(errs);
                        }
                    };
                    match ret.entry(key) {
                        Entry::Occupied(orig) => {
                            let HeaderValue(orig_loc, _): &HeaderValue<Span> = orig.get();
                            add_duplicate_occurrence(
                                &mut errs,
                                HeaderErrorKind::DuplicateEntry,
                                *orig_loc,
                                key_loc,
                            )
                        }
                        Entry::Vacant(entry) => {
                            entry.insert(HeaderValue(key_loc, val));
                        }
                    }
                    if let Some(j) = self.lookahead_is(",", j) {
                        i = self.parse_ws(j);
                        continue;
                    } else {
                        i = self.parse_ws(j);
                        break;
                    }
                }
                if let Some(j) = self.lookahead_is("*", i) {
                    errs.push(HeaderError {
                        kind: HeaderErrorKind::UnexpectedToken(
                            '*',
                            "perhaps this is a glob, in which case it requires string quoting.",
                        ),
                        locations: vec![Span::new(i, j)],
                    });
                    Err(errs)
                } else if let Some(i) = self.lookahead_is("}", i) {
                    if errs.is_empty() {
                        Ok((ret, i))
                    } else {
                        Err(errs)
                    }
                } else {
                    errs.push(HeaderError {
                        kind: HeaderErrorKind::ExpectedToken('}'),
                        locations: vec![Span::new(section_start_pos, i)],
                    });
                    Err(errs)
                }
            } else {
                errs.push(HeaderError {
                    kind: HeaderErrorKind::ExpectedToken('{'),
                    locations: vec![Span::new(i, i)],
                });
                Err(errs)
            }
        } else if self.required {
            errs.push(HeaderError {
                kind: HeaderErrorKind::MissingGrmtoolsSection,
                locations: vec![Span::new(0, 0)],
            });
            Err(errs)
        } else {
            Ok((Header::new(), 0))
        }
    }

    fn parse_name(&self, i: usize) -> Result<(String, usize), HeaderError<Span>> {
        match RE_NAME.find(&self.src[i..]) {
            Some(m) => {
                assert_eq!(m.start(), 0);
                Ok((self.src[i..i + m.end()].to_string(), i + m.end()))
            }
            None => {
                if self.src[i..].starts_with("*") {
                    Err(HeaderError {
                        kind: HeaderErrorKind::UnexpectedToken(
                            '*',
                            "perhaps this is a glob, in which case it requires string quoting.",
                        ),
                        locations: vec![Span::new(i, i)],
                    })
                } else {
                    Err(HeaderError {
                        kind: HeaderErrorKind::IllegalName,
                        locations: vec![Span::new(i, i)],
                    })
                }
            }
        }
    }

    fn lookahead_is(&self, s: &'static str, i: usize) -> Option<usize> {
        if self.src[i..].starts_with(s) {
            Some(i + s.len())
        } else {
            None
        }
    }

    fn parse_ws(&self, i: usize) -> usize {
        RE_LEADING_WS
            .find(&self.src[i..])
            .map(|m| m.end() + i)
            .unwrap_or(i)
    }
}

/// A data structure representation of the %grmtools section.
#[doc(hidden)]
pub type Header<T> = MarkMap<String, HeaderValue<T>>;

impl TryFrom<YaccKind> for Value<Location> {
    type Error = HeaderError<Location>;
    fn try_from(kind: YaccKind) -> Result<Value<Location>, HeaderError<Location>> {
        let from_loc = Location::Other("From<YaccKind>".to_string());
        Ok(Value::Namespaced(format!("YaccKind::{kind:?}"), from_loc))
    }
}

impl<T: Clone> TryFrom<&Value<T>> for YaccKind {
    type Error = HeaderError<T>;
    fn try_from(value: &Value<T>) -> Result<YaccKind, HeaderError<T>> {
        match value {
            Value::Namespaced(kind, loc) => match kind.as_str() {
                "YaccKind::Grmtools" | "Grmtools" => Ok(YaccKind::Grmtools),
                "YaccKind::Eco" | "Eco" => Ok(YaccKind::Eco),
                "YaccKind::Original(UserAction)"
                | "Original(UserAction)"
                | "Original(YaccOriginalActionKind::UserAction)"
                | "YaccKind::Original(YaccOriginalActionKind::UserAction)" => {
                    Ok(YaccKind::Original(YaccOriginalActionKind::UserAction))
                }
                "YaccKind::Original(NoAction)"
                | "Original(NoAction)"
                | "Original(YaccOriginalActionKind::NoAction)"
                | "YaccKind::Original(YaccOriginalActionKind::NoAction)" => {
                    Ok(YaccKind::Original(YaccOriginalActionKind::NoAction))
                }
                "YaccKind::Original(GenericParseTree)"
                | "Original(GenericParseTree)"
                | "Original(YaccOriginalActionKind::GenericParseTree)"
                | "YaccKind::Original(YaccOriginalActionKind::GenericParseTree)" => {
                    Ok(YaccKind::Original(YaccOriginalActionKind::GenericParseTree))
                }
                _ => Err(HeaderError {
                    kind: HeaderErrorKind::InvalidEntry("cfgrammar.yacckind"),
                    locations: vec![loc.clone()],
                }),
            },
            val => Err(HeaderError {
                kind: HeaderErrorKind::InvalidEntry("cfgrammar.yacckind"),
                locations: vec![val.primary_location().clone()],
            }),
        }
    }
}

impl<T> Value<T> {
    #[doc(hidden)]
    pub fn primary_location(&self) -> &T {
        match self {
            Self::Array(_, loc)
            | Self::Bool(_, loc)
            | Self::Num(_, loc)
            | Self::Namespaced(_, loc)
            | Self::String(_, loc) => loc,
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_header_missing_curly_bracket() {
        let srcs = [
            "%grmtools { a",
            "%grmtools { a, b",
            "%grmtools { a, b,",
            "%grmtools { yacckind",
            "%grmtools { yacckind:",
            "%grmtools { yacckind: GrmTools",
            "%grmtools { yacckind: GrmTools,",
            r#"%grmtools { test_files: ""#,
            r#"%grmtools { test_files: "test"#,
            r#"%grmtools { test_files: "test""#,
            r#"%grmtools { test_files: "test","#,
            "%grmtools { !flag",
            "%grmtools { !flag,",
        ];
        for src in srcs {
            for flag in [true, false] {
                let parser = GrmtoolsSectionParser::new(src, flag);
                let res = parser.parse();
                assert!(res.is_err());
            }
        }
    }

    #[test]
    fn test_header_missing_curly_bracket_empty() {
        let src = "%grmtools {";
        for flag in [true, false] {
            let parser = GrmtoolsSectionParser::new(src, flag);
            let res = parser.parse();
            assert!(res.is_err());
        }
    }

    #[test]
    fn test_header_missing_curly_bracket_invalid() {
        let src = "%grmtools {####";
        for flag in [true, false] {
            let parser = GrmtoolsSectionParser::new(src, flag);
            let res = parser.parse();
            assert!(res.is_err());
        }
    }

    #[test]
    fn test_header_duplicates() {
        let src = "%grmtools {dupe, !dupe, dupe: test}";
        for flag in [true, false] {
            let parser = GrmtoolsSectionParser::new(src, flag);
            let res = parser.parse();
            let errs = res.unwrap_err();
            assert_eq!(errs.len(), 1);
            assert_eq!(errs[0].kind, HeaderErrorKind::DuplicateEntry);
            assert_eq!(errs[0].locations.len(), 3);
        }
    }

    #[test]
    fn test_unquoted_globs() {
        let srcs = [
            "%grmtools {test_files: *.test,}",
            "%grmtools {test_files: foo*.test,}",
        ];
        for src in srcs {
            let parser = GrmtoolsSectionParser::new(src, true);
            let res = parser.parse();
            let errs = res.unwrap_err();
            assert_eq!(errs.len(), 1);
            match errs[0] {
                HeaderError {
                    kind: HeaderErrorKind::UnexpectedToken('*', _),
                    locations: _,
                } => (),
                _ => panic!("Expected glob specific error"),
            }
        }
    }
}
