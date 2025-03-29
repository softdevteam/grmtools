use crate::Span;
use lazy_static::lazy_static;
use regex::{Regex, RegexBuilder};

#[derive(Debug)]
#[non_exhaustive]
#[doc(hidden)]
pub enum HeaderError {
    MissingGrmtoolsSection(Span),
    IllegalName(Span),
    ExpectedToken(char, Span),
}

#[derive(Debug, Eq, PartialEq)]
#[doc(hidden)]
pub enum ValBind<'a> {
    FalseKey(&'a str, Span),
    TrueKey(&'a str, Span),
    Bind((&'a str, Span), Val<'a>),
}

#[derive(Debug, Eq, PartialEq)]
#[doc(hidden)]
pub enum Path<'a> {
    Ident(&'a str, Span),
    Scoped((&'a str, Span), (&'a str, Span)),
}

#[derive(Debug, Eq, PartialEq)]
#[doc(hidden)]
pub enum Val<'a> {
    PathLike(Path<'a>),
    ArgLike(Path<'a>, Path<'a>),
    Num(u64, Span),
}

/// Parser for the `%grmtools` section
#[doc(hidden)]
pub struct GrmtoolsSectionParser<'input> {
    src: &'input str,
    required: bool,
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

impl<'input> GrmtoolsSectionParser<'input> {
    pub fn parse_valbind(&'_ self, mut i: usize) -> Result<(ValBind<'_>, usize), HeaderError> {
        if let Some(i) = self.lookahead_is("!", i) {
            let (flag_name, j) = self.parse_name(i)?;
            Ok((
                ValBind::FalseKey(flag_name, Span::new(i, j)),
                self.parse_ws(j),
            ))
        } else {
            let (key_name, j) = self.parse_name(i)?;
            let key_span = Span::new(i, j);
            i = self.parse_ws(j);
            if let Some(j) = self.lookahead_is(":", i) {
                i = self.parse_ws(j);
                match RE_DIGITS.find(&self.src[i..]) {
                    Some(m) => {
                        let num_span = Span::new(i + m.start(), i + m.end());
                        let num_str = &self.src[num_span.start()..num_span.end()];
                        // If the above regex matches we expect this to succeed.
                        let num = str::parse::<u64>(num_str).unwrap();
                        let val = Val::Num(num, num_span);
                        i = self.parse_ws(num_span.end());
                        Ok((ValBind::Bind((key_name, key_span), val), i))
                    }
                    None => {
                        let (path_val, j) = self.parse_path(i)?;
                        i = self.parse_ws(j);
                        if let Some(j) = self.lookahead_is("(", i) {
                            let (arg, j) = self.parse_path(j)?;
                            i = self.parse_ws(j);
                            if let Some(j) = self.lookahead_is(")", i) {
                                i = self.parse_ws(j);
                                Ok((
                                    ValBind::Bind(
                                        (key_name, key_span),
                                        Val::ArgLike(path_val, arg),
                                    ),
                                    i,
                                ))
                            } else {
                                Err(HeaderError::ExpectedToken(')', Span::new(i, i)))
                            }
                        } else {
                            Ok((
                                ValBind::Bind((key_name, key_span), Val::PathLike(path_val)),
                                i,
                            ))
                        }
                    }
                }
            } else {
                Ok((ValBind::TrueKey(key_name, key_span), i))
            }
        }
    }

    fn parse_path(&'_ self, mut i: usize) -> Result<(Path<'_>, usize), HeaderError> {
        let (name, j) = self.parse_name(i)?;
        let name_span = Span::new(i, j);
        i = self.parse_ws(j);
        if let Some(j) = self.lookahead_is("::", i) {
            i = self.parse_ws(j);
            let (scoped_val, j) = self.parse_name(i)?;
            let scoped_span = Span::new(i, j);
            i = self.parse_ws(j);
            Ok((
                Path::Scoped((name, name_span), (scoped_val, scoped_span)),
                i,
            ))
        } else {
            Ok((Path::Ident(name, name_span), i))
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

    pub fn parse(&'_ self) -> Result<(Vec<ValBind<'_>>, usize), HeaderError> {
        if let Some(mut i) = self.lookahead_is(MAGIC, 0) {
            let mut vals = vec![];
            i = self.parse_ws(i);
            let section_start_pos = i;
            if let Some(j) = self.lookahead_is("{", i) {
                i = self.parse_ws(j);
                while self.lookahead_is("}", i).is_none() && i < self.src.len() {
                    let (val, j) = self.parse_valbind(i)?;
                    vals.push(val);
                    if let Some(j) = self.lookahead_is(",", j) {
                        i = self.parse_ws(j);
                        continue;
                    } else {
                        i = j;
                        break;
                    }
                }
                if self.lookahead_is("}", i).is_some() {
                    Ok((vals, i))
                } else {
                    Err(HeaderError::ExpectedToken(
                        '}',
                        Span::new(section_start_pos, self.src.len()),
                    ))
                }
            } else {
                Err(HeaderError::ExpectedToken('{', Span::new(i, i)))
            }
        } else if self.required {
            Err(HeaderError::MissingGrmtoolsSection(Span::new(0, 0)))
        } else {
            Ok((vec![], 0))
        }
    }

    fn parse_name(&self, i: usize) -> Result<(&str, usize), HeaderError> {
        match RE_NAME.find(&self.src[i..]) {
            Some(m) => {
                assert_eq!(m.start(), 0);
                Ok((&self.src[i..i + m.end()], i + m.end()))
            }
            None => Err(HeaderError::IllegalName(Span::new(i, i))),
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
}
