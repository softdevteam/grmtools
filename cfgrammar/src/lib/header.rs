use crate::Span;
use lazy_static::lazy_static;
use regex::Regex;

#[derive(Debug)]
#[non_exhaustive]
pub enum HeaderError {
    MissingGrmtoolsSection(Span),
    IllegalName(Span),
    ExpectedToken(char, Span),
}

#[derive(Debug, Eq, PartialEq)]
pub enum ValBind<'a> {
    // ! [A-Za-z]+
    FalseKey(&'a str, Span),
    // [A-Za-z]+
    TrueKey(&'a str, Span),
    // ([A-Za-z]+ ':' VAL)
    Bind((&'a str, Span), Val<'a>),
}

#[derive(Debug, Eq, PartialEq)]
pub enum Path<'a> {
    // [A-Za-z]+
    Ident(&'a str, Span),
    // ([A-Za-z]+ '::' [A-Za-z]+)
    Scoped((&'a str, Span), (&'a str, Span)),
}

#[derive(Debug, Eq, PartialEq)]
pub enum Val<'a> {
    // PATH
    PathLike(Path<'a>),
    // PATH1 '(' PATH2 ')'
    ArgLike(Path<'a>, Path<'a>),
    // [0-9]+
    Num(u64, Span),
}

/// Parser for the `%grmtools` section
pub struct GrmtoolsSectionParser<'input> {
    src: &'input str,
    required: bool,
}

lazy_static! {
    static ref RE_LEADING_WS: Regex = Regex::new(r"^[\p{Pattern_White_Space}]*").unwrap();
    static ref RE_NAME: Regex = Regex::new(r"^[a-zA-Z][a-zA-Z_]*").unwrap();
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

    pub fn new(src: &'input str, required: bool) -> Self {
        Self { src, required }
    }

    pub fn parse(&'_ self) -> Result<(Vec<ValBind<'_>>, usize), HeaderError> {
        if let Some(mut i) = self.lookahead_is(MAGIC, 0) {
            let mut vals = vec![];
            i = self.parse_ws(i);
            if let Some(j) = self.lookahead_is("{", i) {
                i = self.parse_ws(j);
                while self.lookahead_is("}", i).is_none() {
                    let (val, j) = self.parse_valbind(i)?;
                    vals.push(val);
                    if let Some(j) = self.lookahead_is(",", j) {
                        i = self.parse_ws(j);
                        continue;
                    } else {
                        return Ok((vals, j));
                    }
                }
                Ok((vals, i))
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
