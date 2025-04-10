use crate::{
    markmap::{Entry, MarkMap},
    yacc::{ParserError, YaccKind, YaccOriginalActionKind},
    Location, Span,
};
use lazy_static::lazy_static;
use regex::{Regex, RegexBuilder};
use std::{error::Error, fmt};

/// An error regarding the `%grmtools` header section.
///
/// It could be any of:
///
/// * An error during parsing the section.
/// * An error resulting from a value in the section having an invalid value.
#[derive(Debug, Clone)]
pub struct HeaderError {
    pub kind: HeaderErrorKind,
    pub locations: Vec<Location>,
}

impl Error for HeaderError {}
impl fmt::Display for HeaderError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.kind)
    }
}

impl From<HeaderError> for ParserError {
    fn from(e: HeaderError) -> ParserError {
        ParserError::HeaderError(e)
    }
}

#[derive(Debug, Eq, PartialEq, Copy, Clone)]
#[non_exhaustive]
#[doc(hidden)]
pub enum HeaderErrorKind {
    MissingGrmtoolsSection,
    IllegalName,
    ExpectedToken(char),
    DuplicateEntry,
    InvalidEntry(&'static str),
    ConversionError(&'static str, &'static str),
}

impl fmt::Display for HeaderErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let s = match self {
            HeaderErrorKind::MissingGrmtoolsSection => "Missing %grmtools section",
            HeaderErrorKind::IllegalName => "Illegal name",
            HeaderErrorKind::ExpectedToken(c) => &format!("Expected token: '{}", c),
            HeaderErrorKind::InvalidEntry(s) => &format!("Invalid entry: '{}'", s),
            HeaderErrorKind::DuplicateEntry => "Duplicate Entry",
            HeaderErrorKind::ConversionError(t, err_str) => {
                &format!("Converting header value to type '{}': {}", t, err_str)
            }
        };
        write!(f, "{}", s)
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
pub struct Namespaced {
    pub namespace: Option<(String, Location)>,
    pub member: (String, Location),
}

#[derive(Debug, Eq, PartialEq)]
#[doc(hidden)]
pub enum Setting {
    /// A value like `YaccKind::Grmtools`
    Unitary(Namespaced),
    /// A value like `YaccKind::Original(UserActions)`.
    /// In that example the field ctor would be: `Namespaced { namespace: "YaccKind", member: "Original" }`.
    /// The field would be `Namespaced{ None, UserActions }`.
    Constructor {
        ctor: Namespaced,
        arg: Namespaced,
    },
    Num(u64, Location),
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
pub enum Value {
    Flag(bool, Location),
    Setting(Setting),
}

lazy_static! {
    static ref RE_LEADING_WS: Regex = Regex::new(r"^[\p{Pattern_White_Space}]*").unwrap();
    static ref RE_NAME: Regex = RegexBuilder::new(r"^[A-Z][A-Z_]*")
        .case_insensitive(true)
        .build()
        .unwrap();
    static ref RE_DIGITS: Regex = Regex::new(r"^[0-9]+").unwrap();
}

const MAGIC: &str = "%grmtools";

fn add_duplicate_occurrence(
    errs: &mut Vec<HeaderError>,
    kind: HeaderErrorKind,
    orig_loc: Location,
    dup_loc: Location,
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
    pub fn parse_value(
        &'_ self,
        mut i: usize,
    ) -> Result<(String, Location, Value, usize), HeaderError> {
        if let Some(j) = self.lookahead_is("!", i) {
            let (flag_name, k) = self.parse_name(j)?;
            Ok((
                flag_name,
                Location::Span(Span::new(j, k)),
                Value::Flag(false, Location::Span(Span::new(i, k))),
                self.parse_ws(k),
            ))
        } else {
            let (key_name, j) = self.parse_name(i)?;
            let key_span = Location::Span(Span::new(i, j));
            i = self.parse_ws(j);
            if let Some(j) = self.lookahead_is(":", i) {
                i = self.parse_ws(j);
                match RE_DIGITS.find(&self.src[i..]) {
                    Some(m) => {
                        let num_span = Span::new(i + m.start(), i + m.end());
                        let num_str = &self.src[num_span.start()..num_span.end()];
                        // If the above regex matches we expect this to succeed.
                        let num = str::parse::<u64>(num_str).unwrap();
                        let val = Setting::Num(num, Location::Span(num_span));
                        i = self.parse_ws(num_span.end());
                        Ok((key_name, key_span, Value::Setting(val), i))
                    }
                    None => {
                        let (path_val, j) = self.parse_namespaced(i)?;
                        i = self.parse_ws(j);
                        if let Some(j) = self.lookahead_is("(", i) {
                            let (arg, j) = self.parse_namespaced(j)?;
                            i = self.parse_ws(j);
                            if let Some(j) = self.lookahead_is(")", i) {
                                i = self.parse_ws(j);
                                Ok((
                                    key_name,
                                    key_span,
                                    Value::Setting(Setting::Constructor {
                                        ctor: path_val,
                                        arg,
                                    }),
                                    i,
                                ))
                            } else {
                                Err(HeaderError {
                                    kind: HeaderErrorKind::ExpectedToken(')'),
                                    locations: vec![Location::Span(Span::new(i, i))],
                                })
                            }
                        } else {
                            Ok((
                                key_name,
                                key_span,
                                Value::Setting(Setting::Unitary(path_val)),
                                i,
                            ))
                        }
                    }
                }
            } else {
                Ok((key_name, key_span.clone(), Value::Flag(true, key_span), i))
            }
        }
    }

    fn parse_namespaced(&self, mut i: usize) -> Result<(Namespaced, usize), HeaderError> {
        // Either a name alone, or a namespace which will be followed by a member.
        let (name, j) = self.parse_name(i)?;
        let name_span = Location::Span(Span::new(i, j));
        i = self.parse_ws(j);
        if let Some(j) = self.lookahead_is("::", i) {
            i = self.parse_ws(j);
            let (member_val, j) = self.parse_name(i)?;
            let member_val_span = Location::Span(Span::new(i, j));
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
    pub fn parse(&'_ self) -> Result<(Header, usize), Vec<HeaderError>> {
        let mut errs = Vec::new();
        if let Some(mut i) = self.lookahead_is(MAGIC, self.parse_ws(0)) {
            let mut ret = Header::new();
            i = self.parse_ws(i);
            let section_start_pos = i;
            if let Some(j) = self.lookahead_is("{", i) {
                i = self.parse_ws(j);
                while self.lookahead_is("}", i).is_none() && i < self.src.len() {
                    let (key, key_loc, val, j) = match self.parse_value(i) {
                        Ok((key, key_loc, val, pos)) => (key, key_loc, val, pos),
                        Err(e) => {
                            errs.push(e);
                            return Err(errs);
                        }
                    };
                    match ret.entry(key) {
                        Entry::Occupied(orig) => {
                            let (orig_loc, _): &(Location, Value) = orig.get();
                            add_duplicate_occurrence(
                                &mut errs,
                                HeaderErrorKind::DuplicateEntry,
                                orig_loc.clone(),
                                key_loc,
                            )
                        }
                        Entry::Vacant(entry) => {
                            entry.insert((key_loc, val));
                        }
                    }
                    if let Some(j) = self.lookahead_is(",", j) {
                        i = self.parse_ws(j);
                        continue;
                    } else {
                        i = j;
                        break;
                    }
                }
                if let Some(i) = self.lookahead_is("}", i) {
                    if errs.is_empty() {
                        Ok((ret, i))
                    } else {
                        Err(errs)
                    }
                } else {
                    errs.push(HeaderError {
                        kind: HeaderErrorKind::ExpectedToken('}'),
                        locations: vec![Location::Span(Span::new(
                            section_start_pos,
                            self.src.len(),
                        ))],
                    });
                    Err(errs)
                }
            } else {
                errs.push(HeaderError {
                    kind: HeaderErrorKind::ExpectedToken('{'),
                    locations: vec![Location::Span(Span::new(i, i))],
                });
                Err(errs)
            }
        } else if self.required {
            errs.push(HeaderError {
                kind: HeaderErrorKind::MissingGrmtoolsSection,
                locations: vec![Location::Span(Span::new(0, 0))],
            });
            Err(errs)
        } else {
            Ok((Header::new(), 0))
        }
    }

    fn parse_name(&self, i: usize) -> Result<(String, usize), HeaderError> {
        match RE_NAME.find(&self.src[i..]) {
            Some(m) => {
                assert_eq!(m.start(), 0);
                Ok((
                    self.src[i..i + m.end()].to_string().to_lowercase(),
                    i + m.end(),
                ))
            }
            None => Err(HeaderError {
                kind: HeaderErrorKind::IllegalName,
                locations: vec![Location::Span(Span::new(i, i))],
            }),
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
pub type Header = MarkMap<String, (Location, Value)>;

impl TryFrom<YaccKind> for Value {
    type Error = HeaderError;
    fn try_from(kind: YaccKind) -> Result<Value, HeaderError> {
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

impl TryFrom<&Value> for YaccKind {
    type Error = HeaderError;
    fn try_from(value: &Value) -> Result<YaccKind, HeaderError> {
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
        let src = "%grmtools { a, b";
        for flag in [true, false] {
            let parser = GrmtoolsSectionParser::new(src, flag);
            let res = parser.parse();
            assert!(res.is_err());
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
}
