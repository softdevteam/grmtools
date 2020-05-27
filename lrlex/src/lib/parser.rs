use try_from::TryFrom;

use crate::{lexer::Rule, LexBuildError, LexBuildResult, LexErrorKind};

pub struct LexParser<StorageT> {
    src: String,
    newlines: Vec<usize>,
    pub(crate) rules: Vec<Rule<StorageT>>,
}

impl<StorageT: TryFrom<usize>> LexParser<StorageT> {
    pub(crate) fn new(src: String) -> LexBuildResult<LexParser<StorageT>> {
        let mut p = LexParser {
            src,
            newlines: vec![0],
            rules: Vec::new(),
        };
        p.parse()?;
        Ok(p)
    }

    fn mk_error(&self, kind: LexErrorKind, off: usize) -> LexBuildError {
        let (line, col) = self.off_to_line_col(off);
        LexBuildError { kind, line, col }
    }

    fn off_to_line_col(&self, off: usize) -> (usize, usize) {
        if off == self.src.len() {
            let line_off = *self.newlines.iter().last().unwrap();
            return (
                self.newlines.len(),
                self.src[line_off..].chars().count() + 1,
            );
        }
        let (line_m1, &line_off) = self
            .newlines
            .iter()
            .enumerate()
            .rev()
            .find(|&(_, &line_off)| line_off <= off)
            .unwrap();
        let c_off = self.src[line_off..]
            .char_indices()
            .position(|(c_off, _)| c_off == off - line_off)
            .unwrap();
        (line_m1 + 1, c_off + 1)
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
        if orig_name == ";" {
            name = None;
        } else {
            debug_assert!(!orig_name.is_empty());
            if !((orig_name.starts_with('\'') && orig_name.ends_with('\''))
                || (orig_name.starts_with('\"') && orig_name.ends_with('"')))
            {
                return Err(self.mk_error(LexErrorKind::InvalidName, i + rspace + 1));
            }
            name = Some(orig_name[1..orig_name.len() - 1].to_string());
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

        let rule = Rule::new(Some(tok_id), name, re_str)
            .map_err(|_| self.mk_error(LexErrorKind::RegexError, i))?;
        self.rules.push(rule);
        Ok(i + line_len)
    }

    fn parse_ws(&mut self, i: usize) -> LexBuildResult<usize> {
        let mut j = i;
        for c in self.src[i..].chars() {
            match c {
                ' ' | '\t' => (),
                '\n' | '\r' => self.newlines.push(j + 1),
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
    use crate::lexer::{LRNonStreamingLexerDef, LexerDef};

    #[test]
    fn test_nooptions() {
        let src = "
%option nounput
        "
        .to_string();
        assert!(LRNonStreamingLexerDef::<u8>::from_str(&src).is_err());
    }

    #[test]
    fn test_minimum() {
        let src = "%%".to_string();
        assert!(LRNonStreamingLexerDef::<u8>::from_str(&src).is_ok());
    }

    #[test]
    fn test_rules() {
        let src = "%%
[0-9]+ 'int'
[a-zA-Z]+ 'id'
\\+ '+'
"
        .to_string();
        let ast = LRNonStreamingLexerDef::<u8>::from_str(&src).unwrap();
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
        let ast = LRNonStreamingLexerDef::<u8>::from_str(&src).unwrap();
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
        assert!(LRNonStreamingLexerDef::<u8>::from_str(&src).is_err());
        match LRNonStreamingLexerDef::<u8>::from_str(&src) {
            Ok(_) => panic!("Broken rule parsed"),
            Err(LexBuildError {
                kind: LexErrorKind::MissingSpace,
                line: 2,
                col: 1,
            }) => (),
            Err(e) => panic!("Incorrect error returned {}", e),
        }
    }

    #[test]
    fn test_broken_rule2() {
        let src = "%%
[0-9] "
            .to_string();
        assert!(LRNonStreamingLexerDef::<u8>::from_str(&src).is_err());
        match LRNonStreamingLexerDef::<u8>::from_str(&src) {
            Ok(_) => panic!("Broken rule parsed"),
            Err(LexBuildError {
                kind: LexErrorKind::MissingSpace,
                line: 2,
                col: 1,
            }) => (),
            Err(e) => panic!("Incorrect error returned {}", e),
        }
    }

    #[test]
    fn test_broken_rule3() {
        let src = "%%
[0-9] int"
            .to_string();
        assert!(LRNonStreamingLexerDef::<u8>::from_str(&src).is_err());
        match LRNonStreamingLexerDef::<u8>::from_str(&src) {
            Ok(_) => panic!("Broken rule parsed"),
            Err(LexBuildError {
                kind: LexErrorKind::InvalidName,
                line: 2,
                col: 7,
            }) => (),
            Err(e) => panic!("Incorrect error returned {}", e),
        }
    }

    #[test]
    fn test_broken_rule4() {
        let src = "%%
[0-9] 'int"
            .to_string();
        assert!(LRNonStreamingLexerDef::<u8>::from_str(&src).is_err());
        match LRNonStreamingLexerDef::<u8>::from_str(&src) {
            Ok(_) => panic!("Broken rule parsed"),
            Err(LexBuildError {
                kind: LexErrorKind::InvalidName,
                line: 2,
                col: 7,
            }) => (),
            Err(e) => panic!("Incorrect error returned {}", e),
        }
    }

    #[test]
    fn test_duplicate_rule() {
        let src = "%%
[0-9] 'int'
[0-9] 'int'"
            .to_string();
        match LRNonStreamingLexerDef::<u8>::from_str(&src) {
            Ok(_) => panic!("Duplicate rule parsed"),
            Err(LexBuildError {
                kind: LexErrorKind::DuplicateName,
                line: 3,
                col: 7,
            }) => (),
            Err(e) => panic!("Incorrect error returned {}", e),
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
        LRNonStreamingLexerDef::<u8>::from_str(&src).ok();
    }
}
