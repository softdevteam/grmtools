use cfgrammar::Span;
use try_from::TryFrom;

use crate::{lexer::Rule, LexBuildError, LexBuildResult, LexErrorKind};

pub(super) struct LexParser<StorageT> {
    src: String,
    pub(super) rules: Vec<Rule<StorageT>>,
}

impl<StorageT: TryFrom<usize>> LexParser<StorageT> {
    pub(super) fn new(src: String) -> LexBuildResult<LexParser<StorageT>> {
        let mut p = LexParser {
            src,
            rules: Vec::new(),
        };
        p.parse()?;
        Ok(p)
    }

    fn mk_error(&self, kind: LexErrorKind, off: usize) -> LexBuildError {
        let span = Span::new(off, off);
        LexBuildError { kind, span }
    }

    fn parse(&mut self) -> LexBuildResult<usize> {
        let mut i = self.parse_declarations(0)?;
        i = self.parse_rules(i)?;
        // We don't currently support the subroutines part of a specification. One day we might...
        match self.lookahead_is("%%", i) {
            Some(j) => {
                if self.parse_ws(j)? == self.src.len() {
                    Ok(i)
                } else {
                    Err(self.mk_error(LexErrorKind::RoutinesNotSupported, i))
                }
            }
            None => {
                assert_eq!(i, self.src.len());
                Ok(i)
            }
        }
    }

    fn parse_declarations(&mut self, mut i: usize) -> LexBuildResult<usize> {
        i = self.parse_ws(i)?;
        if let Some(j) = self.lookahead_is("%%", i) {
            return Ok(j);
        }
        if i < self.src.len() {
            Err(self.mk_error(LexErrorKind::UnknownDeclaration, i))
        } else {
            Err(self.mk_error(LexErrorKind::PrematureEnd, i - 1))
        }
    }

    fn parse_rules(&mut self, mut i: usize) -> LexBuildResult<usize> {
        loop {
            i = self.parse_ws(i)?;
            if i == self.src.len() {
                break;
            }
            if self.lookahead_is("%%", i).is_some() {
                break;
            }
            i = self.parse_rule(i)?;
        }
        Ok(i)
    }

    fn parse_rule(&mut self, i: usize) -> LexBuildResult<usize> {
        let line_len = self.src[i..]
            .find(|c| c == '\n')
            .unwrap_or(self.src.len() - i);
        let line = self.src[i..i + line_len].trim_end();
        let rspace = match line.rfind(' ') {
            Some(j) => j,
            None => return Err(self.mk_error(LexErrorKind::MissingSpace, i)),
        };

        let name;
        let orig_name = &line[rspace + 1..];
        let name_span;
        if orig_name == ";" {
            name = None;
            let pos = i + rspace + 1;
            name_span = Span::new(pos, pos);
        } else {
            debug_assert!(!orig_name.is_empty());
            if !((orig_name.starts_with('\'') && orig_name.ends_with('\''))
                || (orig_name.starts_with('\"') && orig_name.ends_with('"')))
            {
                return Err(self.mk_error(LexErrorKind::InvalidName, i + rspace + 1));
            }
            name = Some(orig_name[1..orig_name.len() - 1].to_string());
            name_span = Span::new(i + rspace + 2, i + rspace + orig_name.len());
            let dup_name = self.rules.iter().any(|r| {
                r.name
                    .as_ref()
                    .map_or(false, |n| n == name.as_ref().unwrap())
            });
            if dup_name {
                return Err(self.mk_error(LexErrorKind::DuplicateName, i + rspace + 1));
            }
        }

        let re_str = line[..rspace].trim_end().to_string();
        let rules_len = self.rules.len();
        let tok_id = StorageT::try_from(rules_len)
                           .unwrap_or_else(|_| panic!("StorageT::try_from failed on {} (if StorageT is an unsigned integer type, this probably means that {} exceeds the type's maximum value)", rules_len, rules_len));

        let rule = Rule::new(Some(tok_id), name, name_span, re_str)
            .map_err(|_| self.mk_error(LexErrorKind::RegexError, i))?;
        self.rules.push(rule);
        Ok(i + line_len)
    }

    fn parse_ws(&mut self, i: usize) -> LexBuildResult<usize> {
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

    macro_rules! incorrect_err {
        ($src:ident, $e:ident) => {{
            let mut line_cache = ::cfgrammar::newlinecache::NewlineToLineColCache::default();
            line_cache.feed(&$src);
            if let Some((line, column)) = line_cache.byte_to_line_and_col(&$src, $e.span.start()) {
                panic!(
                    "Incorrect error returned {} at line {line} column {column}",
                    $e
                )
            } else {
                panic!("{}", $e)
            }
        }};
    }

    macro_rules! line_col {
        ($src:ident, $span: ident) => {{
            let mut line_cache = cfgrammar::newlinecache::NewlineToLineColCache::default();
            line_cache.feed(&$src);
            line_cache
                .byte_to_line_and_col(&$src, $span.start())
                .unwrap()
        }};
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
        match LRNonStreamingLexerDef::<DefaultLexeme<u8>, u8>::from_str(&src) {
            Ok(_) => panic!("Broken rule parsed"),
            Err(LexBuildError {
                kind: LexErrorKind::MissingSpace,
                span,
            }) if line_col!(src, span) == (2, 1) => (),
            Err(e) => incorrect_err!(src, e),
        }
    }

    #[test]
    fn test_broken_rule2() {
        let src = "%%
[0-9] "
            .to_string();
        assert!(LRNonStreamingLexerDef::<DefaultLexeme<u8>, u8>::from_str(&src).is_err());
        match LRNonStreamingLexerDef::<DefaultLexeme<u8>, u8>::from_str(&src) {
            Ok(_) => panic!("Broken rule parsed"),
            Err(LexBuildError {
                kind: LexErrorKind::MissingSpace,
                span,
            }) if line_col!(src, span) == (2, 1) => (),
            Err(e) => incorrect_err!(src, e),
        }
    }

    #[test]
    fn test_broken_rule3() {
        let src = "%%
[0-9] int"
            .to_string();
        assert!(LRNonStreamingLexerDef::<DefaultLexeme<u8>, u8>::from_str(&src).is_err());
        match LRNonStreamingLexerDef::<DefaultLexeme<u8>, u8>::from_str(&src) {
            Ok(_) => panic!("Broken rule parsed"),
            Err(LexBuildError {
                kind: LexErrorKind::InvalidName,
                span,
            }) if line_col!(src, span) == (2, 7) => (),
            Err(e) => incorrect_err!(src, e),
        }
    }

    #[test]
    fn test_broken_rule4() {
        let src = "%%
[0-9] 'int"
            .to_string();
        assert!(LRNonStreamingLexerDef::<DefaultLexeme<u8>, u8>::from_str(&src).is_err());
        match LRNonStreamingLexerDef::<DefaultLexeme<u8>, u8>::from_str(&src) {
            Ok(_) => panic!("Broken rule parsed"),
            Err(LexBuildError {
                kind: LexErrorKind::InvalidName,
                span,
            }) if line_col!(src, span) == (2, 7) => (),
            Err(e) => incorrect_err!(src, e),
        }
    }

    #[test]
    fn test_duplicate_rule() {
        let src = "%%
[0-9] 'int'
[0-9] 'int'"
            .to_string();
        match LRNonStreamingLexerDef::<DefaultLexeme<u8>, u8>::from_str(&src) {
            Ok(_) => panic!("Duplicate rule parsed"),
            Err(LexBuildError {
                kind: LexErrorKind::DuplicateName,
                span,
            }) if line_col!(src, span) == (3, 7) => (),
            Err(e) => incorrect_err!(src, e),
        }
    }

    #[test]
    #[should_panic]
    fn exceed_tok_id_capacity() {
        let mut src = "%%
"
        .to_string();
        for i in 0..257 {
            src.push_str(&format!("x 'x{}'\n", i));
        }
        LRNonStreamingLexerDef::<DefaultLexeme<u8>, u8>::from_str(&src).ok();
    }
}
