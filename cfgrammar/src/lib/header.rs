use crate::{yacc::ParserError, Location, Span};
use lazy_static::lazy_static;
use regex::{Regex, RegexBuilder};
use std::collections::{hash_map::Entry, HashMap};
use std::{error::Error, fmt};

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
}

impl fmt::Display for HeaderErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let s = match self {
            HeaderErrorKind::MissingGrmtoolsSection => "Missing %grmtools section",
            HeaderErrorKind::IllegalName => "Illegal name",
            HeaderErrorKind::ExpectedToken(c) => &format!("Expected token: '{}", c),
            HeaderErrorKind::InvalidEntry(s) => &format!("Invalid entry: '{}'", s),
            HeaderErrorKind::DuplicateEntry => "Duplicate Entry",
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

#[derive(Debug, Eq, PartialEq)]
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
    pub fn parse(
        &'_ self,
    ) -> Result<(HashMap<String, (Location, Value)>, usize), Vec<HeaderError>> {
        let mut errs = Vec::new();
        if let Some(mut i) = self.lookahead_is(MAGIC, self.parse_ws(0)) {
            let mut ret = HashMap::new();
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
            Ok((HashMap::new(), 0))
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
