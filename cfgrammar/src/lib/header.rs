use crate::{
    Location, Span, Spanned,
    markmap::{Entry, MarkMap},
    yacc::{
        YaccGrammarError, YaccGrammarErrorKind, YaccKind, YaccOriginalActionKind, parser::SpansKind,
    },
};
use regex::{Regex, RegexBuilder};
use std::{error::Error, fmt, sync::LazyLock};

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
#[derive(Debug, PartialEq)]
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

impl<T> HeaderError<T> {
    /// Returns the [SpansKind] associated with this error.
    pub fn spanskind(&self) -> SpansKind {
        match self.kind {
            HeaderErrorKind::DuplicateEntry => SpansKind::DuplicationError,
            _ => SpansKind::Error,
        }
    }
}

/// Indicates a value prefixed by an optional namespace.
/// `Foo::Bar` with optional `Foo` specified being
/// ```rust,ignore
/// Namespaced{
///     namespace: Some(("Foo", ...)),
///     member: ("Bar", ...)
/// }
/// ```
///
/// Alternately just `Bar` alone without a namespace is represented by :
/// ```rust,ignore
/// Namespaced{
///     namespace: None,
///     member: ("Bar", ...)
/// }
/// ```
#[derive(Debug, Eq, PartialEq)]
#[doc(hidden)]
pub struct Namespaced<T> {
    pub namespace: Option<(String, T)>,
    pub member: (String, T),
}

#[derive(Debug, Eq, PartialEq)]
#[doc(hidden)]
pub enum Setting<T> {
    /// A value like `YaccKind::Grmtools`
    Unitary(Namespaced<T>),
    /// A value like `YaccKind::Original(UserActions)`.
    /// In that example the field ctor would be: `Namespaced { namespace: "YaccKind", member: "Original" }`.
    /// The field would be `Namespaced{ None, UserActions }`.
    Constructor {
        ctor: Namespaced<T>,
        arg: Namespaced<T>,
    },
    Num(u64, T),
    String(String, T),
    // The two `T` values are for the spans of the open and close brackets `[`, and `]`.
    Array(Vec<Setting<T>>, T, T),
}

/// Parser for the `%grmtools` section
#[doc(hidden)]
pub struct GrmtoolsSectionParser<'input> {
    src: &'input str,
    required: bool,
}

/// The value contained within a `Header`
///
/// To be useful across diverse crates this types fields are limited to types derived from `core::` types.
/// like booleans, numeric types, and string values.
#[derive(Debug, Eq, PartialEq)]
#[doc(hidden)]
pub enum Value<T> {
    Flag(bool, T),
    Setting(Setting<T>),
}

impl From<Setting<Span>> for Setting<Location> {
    fn from(s: Setting<Span>) -> Setting<Location> {
        match s {
            Setting::Unitary(Namespaced {
                namespace,
                member: (m, ml),
            }) => Setting::Unitary(Namespaced {
                namespace: namespace.map(|(n, nl)| (n, nl.into())),
                member: (m, ml.into()),
            }),
            Setting::Constructor {
                ctor:
                    Namespaced {
                        namespace: ctor_ns,
                        member: (ctor_m, ctor_ml),
                    },
                arg:
                    Namespaced {
                        namespace: arg_ns,
                        member: (arg_m, arg_ml),
                    },
            } => Setting::Constructor {
                ctor: Namespaced {
                    namespace: ctor_ns.map(|(ns, ns_l)| (ns, ns_l.into())),
                    member: (ctor_m, ctor_ml.into()),
                },
                arg: Namespaced {
                    namespace: arg_ns.map(|(ns, ns_l)| (ns, ns_l.into())),
                    member: (arg_m, arg_ml.into()),
                },
            },
            Setting::Num(num, num_loc) => Setting::Num(num, num_loc.into()),
            Setting::String(s, str_loc) => Setting::String(s, str_loc.into()),
            Setting::Array(mut xs, arr_open_loc, arr_close_loc) => Setting::Array(
                xs.drain(..).map(|x| x.into()).collect(),
                arr_open_loc.into(),
                arr_close_loc.into(),
            ),
        }
    }
}

impl From<Value<Span>> for Value<Location> {
    fn from(v: Value<Span>) -> Value<Location> {
        match v {
            Value::Flag(flag, u) => Value::Flag(flag, u.into()),
            Value::Setting(s) => Value::Setting(s.into()),
        }
    }
}

impl<T> Value<T> {
    pub fn expect_string_with_context(&self, ctxt: &str) -> Result<&str, Box<dyn Error>> {
        let found = match self {
            Value::Flag(_, _) => "bool".to_string(),
            Value::Setting(Setting::String(s, _)) => {
                return Ok(s);
            }
            Value::Setting(Setting::Num(_, _)) => "numeric".to_string(),
            Value::Setting(Setting::Unitary(Namespaced {
                namespace,
                member: (member, _),
            })) => {
                if let Some((ns, _)) = namespace {
                    format!("'{ns}::{member}'")
                } else {
                    format!("'{member}'")
                }
            }
            Value::Setting(Setting::Array(_, _, _)) => "array".to_string(),
            Value::Setting(Setting::Constructor {
                ctor:
                    Namespaced {
                        namespace: ctor_ns,
                        member: (ctor_memb, _),
                    },
                arg:
                    Namespaced {
                        namespace: arg_ns,
                        member: (arg_memb, _),
                    },
            }) => {
                format!(
                    "'{}({})'",
                    if let Some((ns, _)) = ctor_ns {
                        format!("{ns}::{ctor_memb}")
                    } else {
                        arg_memb.to_string()
                    },
                    if let Some((ns, _)) = arg_ns {
                        format!("{ns}::{arg_memb}")
                    } else {
                        arg_memb.to_string()
                    }
                )
            }
        };
        Err(format!("Expected 'String' value, found {}, at {ctxt}", found).into())
    }
}

static RE_LEADING_WS: LazyLock<Regex> =
    LazyLock::new(|| Regex::new(r"^[\p{Pattern_White_Space}]*").unwrap());
static RE_NAME: LazyLock<Regex> = LazyLock::new(|| {
    RegexBuilder::new(r"^[A-Z][A-Z_]*")
        .case_insensitive(true)
        .build()
        .unwrap()
});
static RE_DIGITS: LazyLock<Regex> = LazyLock::new(|| Regex::new(r"^[0-9]+").unwrap());
static RE_STRING: LazyLock<Regex> = LazyLock::new(|| Regex::new(r#"^\"(\\.|[^"\\])*\""#).unwrap());

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
    fn parse_setting(&'_ self, mut i: usize) -> Result<(Setting<Span>, usize), HeaderError<Span>> {
        i = self.parse_ws(i);
        match RE_DIGITS.find(&self.src[i..]) {
            Some(m) => {
                let num_span = Span::new(i + m.start(), i + m.end());
                let num_str = &self.src[num_span.start()..num_span.end()];
                // If the above regex matches we expect this to succeed.
                let num = str::parse::<u64>(num_str).unwrap();
                let val = Setting::Num(num, num_span);
                i = self.parse_ws(num_span.end());
                Ok((val, i))
            }
            None => match RE_STRING.find(&self.src[i..]) {
                Some(m) => {
                    let end = i + m.end();
                    // Trim the leading and trailing quotes.
                    let str_span = Span::new(i + m.start() + 1, end - 1);
                    let str = &self.src[str_span.start()..str_span.end()];
                    let setting = Setting::String(str.to_string(), str_span);
                    // After the trailing quotes.
                    i = self.parse_ws(end);
                    Ok((setting, i))
                }
                None => {
                    if let Some(mut j) = self.lookahead_is("[", i) {
                        let mut vals = Vec::new();
                        let open_pos = j;

                        loop {
                            j = self.parse_ws(j);
                            if let Some(end_pos) = self.lookahead_is("]", j) {
                                return Ok((
                                    Setting::Array(
                                        vals,
                                        Span::new(i, open_pos),
                                        Span::new(j, end_pos),
                                    ),
                                    end_pos,
                                ));
                            }
                            if let Ok((val, k)) = self.parse_setting(j) {
                                vals.push(val);
                                j = self.parse_ws(k);
                            }
                            if let Some(k) = self.lookahead_is(",", j) {
                                j = k
                            }
                        }
                    } else {
                        let (path_val, j) = self.parse_namespaced(i)?;
                        i = self.parse_ws(j);
                        if let Some(j) = self.lookahead_is("(", i) {
                            let (arg, j) = self.parse_namespaced(j)?;
                            i = self.parse_ws(j);
                            if let Some(j) = self.lookahead_is(")", i) {
                                i = self.parse_ws(j);
                                Ok((
                                    Setting::Constructor {
                                        ctor: path_val,
                                        arg,
                                    },
                                    i,
                                ))
                            } else {
                                Err(HeaderError {
                                    kind: HeaderErrorKind::ExpectedToken(')'),
                                    locations: vec![Span::new(i, i)],
                                })
                            }
                        } else {
                            Ok((Setting::Unitary(path_val), i))
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
                Value::Flag(false, Span::new(i, k)),
                self.parse_ws(k),
            ))
        } else {
            let (key_name, j) = self.parse_name(i)?;
            let key_span = Span::new(i, j);
            i = self.parse_ws(j);
            if let Some(j) = self.lookahead_is(":", i) {
                let (val, j) = self.parse_setting(j)?;
                Ok((key_name, key_span, Value::Setting(val), j))
            } else {
                Ok((key_name, key_span, Value::Flag(true, key_span), i))
            }
        }
    }

    fn parse_namespaced(
        &self,
        mut i: usize,
    ) -> Result<(Namespaced<Span>, usize), HeaderError<Span>> {
        // Either a name alone, or a namespace which will be followed by a member.
        let (name, j) = self.parse_name(i)?;
        let name_span = Span::new(i, j);
        i = self.parse_ws(j);
        if let Some(j) = self.lookahead_is("::", i) {
            i = self.parse_ws(j);
            let (member_val, j) = self.parse_name(i)?;
            let member_val_span = Span::new(i, j);
            i = self.parse_ws(j);
            Ok((
                Namespaced {
                    namespace: Some((name, name_span)),
                    member: (member_val, member_val_span),
                },
                i,
            ))
        } else {
            Ok((
                Namespaced {
                    namespace: None,
                    member: (name, name_span),
                },
                i,
            ))
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
                        Ok((key, key_loc, val, pos)) => (key, key_loc, val, pos),
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
                Ok((
                    self.src[i..i + m.end()].to_string().to_lowercase(),
                    i + m.end(),
                ))
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
        Ok(match kind {
            YaccKind::Grmtools => Value::Setting(Setting::Unitary(Namespaced {
                namespace: Some(("yacckind".to_string(), from_loc.clone())),
                member: ("grmtools".to_string(), from_loc),
            })),
            YaccKind::Eco => Value::Setting(Setting::Unitary(Namespaced {
                namespace: Some(("yacckind".to_string(), from_loc.clone())),
                member: ("eco".to_string(), from_loc),
            })),
            YaccKind::Original(action_kind) => Value::Setting(Setting::Constructor {
                ctor: Namespaced {
                    namespace: Some(("yacckind".to_string(), from_loc.clone())),
                    member: ("original".to_string(), from_loc.clone()),
                },
                arg: match action_kind {
                    YaccOriginalActionKind::NoAction => Namespaced {
                        namespace: Some(("yaccoriginalactionkind".to_string(), from_loc.clone())),
                        member: ("noaction".to_string(), from_loc),
                    },
                    YaccOriginalActionKind::UserAction => Namespaced {
                        namespace: Some(("yaccoriginalactionkind".to_string(), from_loc.clone())),
                        member: ("useraction".to_string(), from_loc),
                    },
                    YaccOriginalActionKind::GenericParseTree => Namespaced {
                        namespace: Some(("yaccoriginalactionkind".to_string(), from_loc.clone())),
                        member: ("genericparsetree".to_string(), from_loc),
                    },
                },
            }),
        })
    }
}

impl<T: Clone> TryFrom<&Value<T>> for YaccKind {
    type Error = HeaderError<T>;
    fn try_from(value: &Value<T>) -> Result<YaccKind, HeaderError<T>> {
        let mut err_locs = Vec::new();
        match value {
            Value::Flag(_, loc) => Err(HeaderError {
                kind: HeaderErrorKind::ConversionError(
                    "From<YaccKind>",
                    "Cannot convert boolean to YaccKind",
                ),
                locations: vec![loc.clone()],
            }),
            Value::Setting(Setting::Num(_, loc)) => Err(HeaderError {
                kind: HeaderErrorKind::ConversionError(
                    "From<YaccKind>",
                    "Cannot convert number to YaccKind",
                ),
                locations: vec![loc.clone()],
            }),
            Value::Setting(Setting::Array(_, loc, _)) => Err(HeaderError {
                kind: HeaderErrorKind::ConversionError(
                    "From<YaccKind>",
                    "Cannot convert array to YaccKind",
                ),
                locations: vec![loc.clone()],
            }),
            Value::Setting(Setting::String(_, loc)) => Err(HeaderError {
                kind: HeaderErrorKind::ConversionError(
                    "From<YaccKind>",
                    "Cannot convert string to YaccKind",
                ),
                locations: vec![loc.clone()],
            }),

            Value::Setting(Setting::Unitary(Namespaced {
                namespace,
                member: (yk_value, yk_value_loc),
            })) => {
                if let Some((ns, ns_loc)) = namespace {
                    if ns != "yacckind" {
                        err_locs.push(ns_loc.clone());
                    }
                }
                let yacckinds = [
                    ("grmtools".to_string(), YaccKind::Grmtools),
                    ("eco".to_string(), YaccKind::Eco),
                ];
                let yk_found = yacckinds
                    .iter()
                    .find_map(|(yk_str, yk)| (yk_str == yk_value).then_some(yk));
                if let Some(yk) = yk_found {
                    if err_locs.is_empty() {
                        Ok(*yk)
                    } else {
                        Err(HeaderError {
                            kind: HeaderErrorKind::InvalidEntry("yacckind"),
                            locations: err_locs,
                        })
                    }
                } else {
                    err_locs.push(yk_value_loc.clone());
                    Err(HeaderError {
                        kind: HeaderErrorKind::InvalidEntry("yacckind"),
                        locations: err_locs,
                    })
                }
            }
            Value::Setting(Setting::Constructor {
                ctor:
                    Namespaced {
                        namespace: yk_namespace,
                        member: (yk_str, yk_loc),
                    },
                arg:
                    Namespaced {
                        namespace: ak_namespace,
                        member: (ak_str, ak_loc),
                    },
            }) => {
                if let Some((yk_ns, yk_ns_loc)) = yk_namespace {
                    if yk_ns != "yacckind" {
                        err_locs.push(yk_ns_loc.clone());
                    }
                }

                if yk_str != "original" {
                    err_locs.push(yk_loc.clone());
                }

                if let Some((ak_ns, ak_ns_loc)) = ak_namespace {
                    if ak_ns != "yaccoriginalactionkind" {
                        err_locs.push(ak_ns_loc.clone());
                    }
                }
                let actionkinds = [
                    ("noaction", YaccOriginalActionKind::NoAction),
                    ("useraction", YaccOriginalActionKind::UserAction),
                    ("genericparsetree", YaccOriginalActionKind::GenericParseTree),
                ];
                let yk_found = actionkinds.iter().find_map(|(actionkind_str, actionkind)| {
                    (ak_str == actionkind_str).then_some(YaccKind::Original(*actionkind))
                });

                if let Some(yk) = yk_found {
                    if err_locs.is_empty() {
                        Ok(yk)
                    } else {
                        Err(HeaderError {
                            kind: HeaderErrorKind::InvalidEntry("yacckind"),
                            locations: err_locs,
                        })
                    }
                } else {
                    err_locs.push(ak_loc.clone());
                    Err(HeaderError {
                        kind: HeaderErrorKind::InvalidEntry("yacckind"),
                        locations: err_locs,
                    })
                }
            }
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
