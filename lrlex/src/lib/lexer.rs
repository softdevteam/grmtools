use std::{
    collections::{HashMap, HashSet},
    hash::Hash,
    marker::PhantomData,
    slice::Iter
};

use num_traits::{PrimInt, Unsigned};
use regex::{self, Regex, RegexBuilder};

use lrpar::{LexError, Lexeme, Lexer, Span};

pub struct Rule<StorageT> {
    /// If `Some`, the ID that lexemes created against this rule will be given (lrlex gives such
    /// rules a guaranteed unique value, though that value can be overridden by clients who need to
    /// control the ID). If `None`, then this rule specifies lexemes which should not appear in the
    /// user's input.
    pub tok_id: Option<StorageT>,
    /// This rule's name. If None, then text which matches this rule will be skipped (i.e. will not
    /// create a lexeme).
    pub name: Option<String>,
    pub re_str: String,
    pub re: Regex
}

impl<StorageT> Rule<StorageT> {
    /// Create a new `Rule`. This interface is unstable and should only be used by code generated
    /// by lrlex itself.
    #[doc(hidden)]
    pub fn new(
        tok_id: Option<StorageT>,
        name: Option<String>,
        re_str: String
    ) -> Result<Rule<StorageT>, regex::Error> {
        let re = RegexBuilder::new(&format!("\\A(?:{})", &re_str))
            .multi_line(true)
            .dot_matches_new_line(true)
            .build()?;
        Ok(Rule {
            tok_id,
            name,
            re_str,
            re
        })
    }
}

/// This struct represents, in essence, a .l file in memory. From it one can produce a `Lexer`
/// which actually lexes inputs.
pub struct LexerDef<StorageT> {
    pub(crate) rules: Vec<Rule<StorageT>>
}

impl<StorageT: Copy + Eq + Hash + PrimInt + Unsigned> LexerDef<StorageT> {
    pub fn new(rules: Vec<Rule<StorageT>>) -> LexerDef<StorageT> {
        LexerDef { rules }
    }

    /// Get the `Rule` at index `idx`.
    pub fn get_rule(&self, idx: usize) -> Option<&Rule<StorageT>> {
        self.rules.get(idx)
    }

    /// Get the `Rule` instance associated with a particular lexeme ID. Panics if no such rule
    /// exists.
    pub fn get_rule_by_id(&self, tok_id: StorageT) -> &Rule<StorageT> {
        &self
            .rules
            .iter()
            .find(|r| r.tok_id == Some(tok_id))
            .unwrap()
    }

    /// Get the `Rule` instance associated with a particular name.
    pub fn get_rule_by_name(&self, n: &str) -> Option<&Rule<StorageT>> {
        self.rules
            .iter()
            .find(|r| r.name.as_ref().map(String::as_str) == Some(n))
    }

    /// Set the id attribute on rules to the corresponding value in `map`. This is typically used
    /// to synchronise a parser's notion of lexeme IDs with the lexers. While doing this, it keeps
    /// track of which lexemes:
    ///   1) are defined in the lexer but not referenced by the parser
    ///   2) and referenced by the parser but not defined in the lexer
    /// and returns them as a tuple `(Option<HashSet<&str>>, Option<HashSet<&str>>)` in the order
    /// (*defined_in_lexer_missing_from_parser*, *referenced_in_parser_missing_from_lexer*). Since
    /// in most cases both sets are expected to be empty, `None` is returned to avoid a `HashSet`
    /// allocation.
    ///
    /// Lexing and parsing can continue if either set is non-empty, so it is up to the caller as to
    /// what action they take if either return set is non-empty. A non-empty set #1 is often
    /// benign: some lexers deliberately define tokens which are not used (e.g. reserving future
    /// keywords). A non-empty set #2 is more likely to be an error since there are parts of the
    /// grammar where nothing the user can input will be parseable.
    pub fn set_rule_ids<'a>(
        &'a mut self,
        rule_ids_map: &HashMap<&'a str, StorageT>
    ) -> (Option<HashSet<&'a str>>, Option<HashSet<&'a str>>) {
        // Because we have to iter_mut over self.rules, we can't easily store a reference to the
        // rule's name at the same time. Instead, we store the index of each such rule and
        // recover the names later.
        let mut missing_from_parser_idxs = Vec::new();
        let mut rules_with_names = 0;
        for (i, r) in self.rules.iter_mut().enumerate() {
            if let Some(ref n) = r.name {
                match rule_ids_map.get(&**n) {
                    Some(tok_id) => r.tok_id = Some(*tok_id),
                    None => {
                        r.tok_id = None;
                        missing_from_parser_idxs.push(i);
                    }
                }
                rules_with_names += 1;
            }
        }

        let missing_from_parser;
        if missing_from_parser_idxs.is_empty() {
            missing_from_parser = None;
        } else {
            let mut mfp = HashSet::with_capacity(missing_from_parser_idxs.len());
            for i in &missing_from_parser_idxs {
                mfp.insert(self.rules[*i].name.as_ref().unwrap().as_str());
            }
            missing_from_parser = Some(mfp);
        };

        let missing_from_lexer;
        if rules_with_names - missing_from_parser_idxs.len() == rule_ids_map.len() {
            missing_from_lexer = None
        } else {
            missing_from_lexer = Some(
                rule_ids_map
                    .keys()
                    .cloned()
                    .collect::<HashSet<&str>>()
                    .difference(
                        &self
                            .rules
                            .iter()
                            .filter(|x| x.name.is_some())
                            .map(|x| &**x.name.as_ref().unwrap())
                            .collect::<HashSet<&str>>()
                    )
                    .cloned()
                    .collect::<HashSet<&str>>()
            );
        }

        (missing_from_lexer, missing_from_parser)
    }

    /// Returns an iterator over all rules in this AST.
    pub fn iter_rules(&self) -> Iter<Rule<StorageT>> {
        self.rules.iter()
    }

    /// Return a lexer for the `String` `s` that will lex relative to this `LexerDef`.
    pub fn lexer<'lexer, 'input: 'lexer>(
        &'lexer self,
        s: &'input str
    ) -> LRLexer<'lexer, 'input, StorageT> {
        LRLexer::new(self, s)
    }
}

/// A lexer holds a reference to a string and can lex it into `Lexeme`s. Although the struct is
/// tied to a single string, no guarantees are made about whether the lexemes are cached or not.
pub struct LRLexer<'lexer, 'input: 'lexer, StorageT> {
    s: &'input str,
    lexemes: Vec<Result<Lexeme<StorageT>, LexError>>,
    newlines: Vec<usize>,
    phantom: PhantomData<&'lexer ()>
}

impl<'lexer, 'input: 'lexer, StorageT: Copy + Eq + Hash + PrimInt + Unsigned>
    LRLexer<'lexer, 'input, StorageT>
{
    fn new(
        lexerdef: &'lexer LexerDef<StorageT>,
        s: &'input str
    ) -> LRLexer<'lexer, 'input, StorageT> {
        let mut lexemes = vec![];
        let mut newlines = vec![];
        let mut i = 0;
        while i < s.len() {
            let old_i = i;
            let mut longest = 0; // Length of the longest match
            let mut longest_ridx = 0; // This is only valid iff longest != 0
            for (ridx, r) in lexerdef.iter_rules().enumerate() {
                if let Some(m) = r.re.find(&s[old_i..]) {
                    let len = m.end();
                    // Note that by using ">", we implicitly prefer an earlier over a later rule, if
                    // both match an input of the same length.
                    if len > longest {
                        longest = len;
                        longest_ridx = ridx;
                    }
                }
            }
            if longest > 0 {
                newlines.extend(
                    s[old_i..old_i + longest]
                        .chars()
                        .enumerate()
                        .filter(|&(_, c)| c == '\n')
                        .map(|(j, _)| old_i + j + 1)
                );
                let r = lexerdef.get_rule(longest_ridx).unwrap();
                if r.name.is_some() {
                    match r.tok_id {
                        Some(tok_id) => {
                            lexemes.push(Ok(Lexeme::new(tok_id, old_i, Some(longest))));
                        }
                        None => {
                            lexemes.push(Err(LexError::new(Span::new(old_i, old_i))));
                            break;
                        }
                    }
                }
                i += longest;
            } else {
                lexemes.push(Err(LexError::new(Span::new(old_i, old_i))));
                break;
            }
        }

        LRLexer {
            s,
            lexemes,
            newlines,
            phantom: PhantomData
        }
    }
}

impl<'lexer, 'input: 'lexer, StorageT: Copy + Eq + Hash + PrimInt + Unsigned>
    Lexer<'input, StorageT> for LRLexer<'lexer, 'input, StorageT>
{
    fn iter<'a>(&'a self) -> Box<dyn Iterator<Item = Result<Lexeme<StorageT>, LexError>> + 'a> {
        Box::new(self.lexemes.iter().cloned())
    }

    fn span_str(&self, span: Span) -> &'input str {
        if span.end() > self.s.len() {
            panic!(
                "Span {:?} exceeds known input length {}",
                span,
                self.s.len()
            );
        }
        &self.s[span.start()..span.end()]
    }

    fn span_lines_str(&self, span: Span) -> &'input str {
        debug_assert!(span.end() >= span.start());
        if span.end() > self.s.len() {
            panic!(
                "Span {:?} exceeds known input length {}",
                span,
                self.s.len()
            );
        }

        fn surrounding_line_off<StorageT>(lexer: &LRLexer<StorageT>, i: usize) -> (usize, usize) {
            if i > lexer.s.len() {
                panic!("Offset {} exceeds known input length {}", i, lexer.s.len());
            }

            if lexer.newlines.is_empty() {
                return (0, lexer.s.len());
            } else if i < lexer.newlines[0] {
                return (0, lexer.newlines[0] - 1);
            }

            for j in 0..lexer.newlines.len() - 1 {
                if lexer.newlines[j + 1] > i {
                    return (lexer.newlines[j], lexer.newlines[j + 1] - 1);
                }
            }
            (lexer.newlines[lexer.newlines.len() - 1], lexer.s.len())
        }

        let (st, _) = surrounding_line_off(self, span.start());
        let (_, en) = surrounding_line_off(self, span.end());
        &self.s[st..en]
    }

    fn line_col(&self, span: Span) -> ((usize, usize), (usize, usize)) {
        debug_assert!(span.end() >= span.start());
        if span.end() > self.s.len() {
            panic!(
                "Span {:?} exceeds known input length {}",
                span,
                self.s.len()
            );
        }

        fn lc_byte<StorageT>(lexer: &LRLexer<StorageT>, i: usize) -> (usize, usize) {
            if lexer.newlines.is_empty() || i < lexer.newlines[0] {
                return (1, i);
            }

            for j in 0..lexer.newlines.len() - 1 {
                if lexer.newlines[j + 1] > i {
                    return (j + 2, i - lexer.newlines[j]);
                }
            }
            (
                lexer.newlines.len() + 1,
                i - lexer.newlines[lexer.newlines.len() - 1]
            )
        }

        fn lc_char<StorageT: Copy + Eq + Hash + PrimInt + Unsigned>(
            lexer: &LRLexer<StorageT>,
            i: usize
        ) -> (usize, usize) {
            let (line_idx, col_byte) = lc_byte(lexer, i);
            let line = lexer.span_lines_str(Span::new(i, i));
            (line_idx, line[..col_byte].chars().count() + 1)
        }

        (lc_char(self, span.start()), lc_char(self, span.end()))
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::parser::parse_lex;
    use std::collections::HashMap;

    #[test]
    fn test_basic() {
        let src = r"
%%
[0-9]+ 'int'
[a-zA-Z]+ 'id'
[ \t] ;
        "
        .to_string();
        let mut lexerdef = parse_lex(&src).unwrap();
        let mut map = HashMap::new();
        map.insert("int", 0);
        map.insert("id", 1);
        assert_eq!(lexerdef.set_rule_ids(&map), (None, None));

        let lexemes = lexerdef
            .lexer(&"abc 123")
            .iter()
            .map(|x| x.unwrap())
            .collect::<Vec<_>>();
        assert_eq!(lexemes.len(), 2);
        let lex1 = lexemes[0];
        assert_eq!(lex1.tok_id(), 1u8);
        assert_eq!(lex1.span().start(), 0);
        assert_eq!(lex1.span().len(), 3);
        let lex2 = lexemes[1];
        assert_eq!(lex2.tok_id(), 0);
        assert_eq!(lex2.span().start(), 4);
        assert_eq!(lex2.span().len(), 3);
    }

    #[test]
    fn test_basic_error() {
        let src = "
%%
[0-9]+ 'int'
        "
        .to_string();
        let lexerdef = parse_lex::<u8>(&src).unwrap();
        match lexerdef.lexer(&"abc").iter().nth(0).unwrap() {
            Ok(_) => panic!("Invalid input lexed"),
            Err(e) => {
                if e.span().start() != 0 || e.span().end() != 0 {
                    panic!("Incorrect span returned {:?}", e.span());
                }
            }
        };
    }

    #[test]
    fn test_longest_match() {
        let src = "%%
if 'IF'
[a-z]+ 'ID'
[ ] ;"
            .to_string();
        let mut lexerdef = parse_lex(&src).unwrap();
        let mut map = HashMap::new();
        map.insert("IF", 0);
        map.insert("ID", 1);
        assert_eq!(lexerdef.set_rule_ids(&map), (None, None));

        let lexemes = lexerdef
            .lexer(&"iff if")
            .iter()
            .map(|x| x.unwrap())
            .collect::<Vec<_>>();
        assert_eq!(lexemes.len(), 2);
        let lex1 = lexemes[0];
        assert_eq!(lex1.tok_id(), 1u8);
        assert_eq!(lex1.span().start(), 0);
        assert_eq!(lex1.span().len(), 3);
        let lex2 = lexemes[1];
        assert_eq!(lex2.tok_id(), 0);
        assert_eq!(lex2.span().start(), 4);
        assert_eq!(lex2.span().len(), 2);
    }

    #[test]
    fn test_multibyte() {
        let src = "%%
[a❤]+ 'ID'
[ ] ;"
            .to_string();
        let mut lexerdef = parse_lex(&src).unwrap();
        let mut map = HashMap::new();
        map.insert("ID", 0u8);
        assert_eq!(lexerdef.set_rule_ids(&map), (None, None));

        let lexer = lexerdef.lexer("a ❤ a");
        let lexemes = lexer.iter().map(|x| x.unwrap()).collect::<Vec<_>>();
        assert_eq!(lexemes.len(), 3);
        let lex1 = lexemes[0];
        assert_eq!(lex1.span().start(), 0);
        assert_eq!(lex1.span().len(), 1);
        assert_eq!(lexer.span_str(lex1.span()), "a");
        let lex2 = lexemes[1];
        assert_eq!(lex2.span().start(), 2);
        assert_eq!(lex2.span().len(), 3);
        assert_eq!(lexer.span_str(lex2.span()), "❤");
        let lex3 = lexemes[2];
        assert_eq!(lex3.span().start(), 6);
        assert_eq!(lex3.span().len(), 1);
        assert_eq!(lexer.span_str(lex3.span()), "a");
    }

    #[test]
    fn test_line_col() {
        let src = "%%
[a-z]+ 'ID'
[ \\n] ;"
            .to_string();
        let mut lexerdef = parse_lex(&src).unwrap();
        let mut map = HashMap::new();
        map.insert("ID", 0u8);
        assert_eq!(lexerdef.set_rule_ids(&map), (None, None));

        let lexer = lexerdef.lexer("a b c");
        let lexemes = lexer.iter().map(|x| x.unwrap()).collect::<Vec<_>>();
        assert_eq!(lexemes.len(), 3);
        assert_eq!(lexer.line_col(lexemes[1].span()), ((1, 3), (1, 4)));
        assert_eq!(lexer.span_lines_str(lexemes[1].span()), "a b c");

        let lexer = lexerdef.lexer("a b c\n");
        let lexemes = lexer.iter().map(|x| x.unwrap()).collect::<Vec<_>>();
        assert_eq!(lexemes.len(), 3);
        assert_eq!(lexer.line_col(lexemes[1].span()), ((1, 3), (1, 4)));
        assert_eq!(lexer.span_lines_str(lexemes[1].span()), "a b c");

        let lexer = lexerdef.lexer(" a\nb\n  c d");
        let lexemes = lexer.iter().map(|x| x.unwrap()).collect::<Vec<_>>();
        assert_eq!(lexemes.len(), 4);
        assert_eq!(lexer.line_col(lexemes[0].span()), ((1, 2), (1, 3)));
        assert_eq!(lexer.line_col(lexemes[1].span()), ((2, 1), (2, 2)));
        assert_eq!(lexer.line_col(lexemes[2].span()), ((3, 3), (3, 4)));
        assert_eq!(lexer.line_col(lexemes[3].span()), ((3, 5), (3, 6)));
        assert_eq!(lexer.span_lines_str(lexemes[0].span()), " a");
        assert_eq!(lexer.span_lines_str(lexemes[1].span()), "b");
        assert_eq!(lexer.span_lines_str(lexemes[2].span()), "  c d");
        assert_eq!(lexer.span_lines_str(lexemes[3].span()), "  c d");
    }

    #[test]
    fn test_line_col_multibyte() {
        let src = "%%
[a-z❤]+ 'ID'
[ \\n] ;"
            .to_string();
        let mut lexerdef = parse_lex(&src).unwrap();
        let mut map = HashMap::new();
        map.insert("ID", 0u8);
        assert_eq!(lexerdef.set_rule_ids(&map), (None, None));

        let lexer = lexerdef.lexer(" a\n❤ b");
        let lexemes = lexer.iter().map(|x| x.unwrap()).collect::<Vec<_>>();
        assert_eq!(lexemes.len(), 3);
        assert_eq!(lexer.line_col(lexemes[0].span()), ((1, 2), (1, 3)));
        assert_eq!(lexer.line_col(lexemes[1].span()), ((2, 1), (2, 2)));
        assert_eq!(lexer.line_col(lexemes[2].span()), ((2, 3), (2, 4)));
        assert_eq!(lexer.span_lines_str(lexemes[0].span()), " a");
        assert_eq!(lexer.span_lines_str(lexemes[1].span()), "❤ b");
        assert_eq!(lexer.span_lines_str(lexemes[2].span()), "❤ b");
    }

    #[test]
    #[should_panic]
    fn test_bad_line_col() {
        let src = "%%
[a-z]+ 'ID'
[ \\n] ;"
            .to_string();
        let mut lexerdef = parse_lex(&src).unwrap();
        let mut map = HashMap::new();
        map.insert("ID", 0u8);
        assert_eq!(lexerdef.set_rule_ids(&map), (None, None));

        let lexer = lexerdef.lexer("a b c");

        lexer.line_col(Span::new(100, 100));
    }

    #[test]
    fn test_missing_from_lexer_and_parser() {
        let src = "%%
[a-z]+ 'ID'
[ \\n] ;"
            .to_string();
        let mut lexerdef = parse_lex(&src).unwrap();
        let mut map = HashMap::new();
        map.insert("INT", 0u8);
        let mut missing_from_lexer = HashSet::new();
        missing_from_lexer.insert("INT");
        let mut missing_from_parser = HashSet::new();
        missing_from_parser.insert("ID");
        assert_eq!(
            lexerdef.set_rule_ids(&map),
            (Some(missing_from_lexer), Some(missing_from_parser))
        );

        match lexerdef.lexer(&" a ").iter().nth(0).unwrap() {
            Ok(_) => panic!("Invalid input lexed"),
            Err(e) => {
                if e.span().start() != 1 || e.span().end() != 1 {
                    panic!("Incorrect span returned {:?}", e.span());
                }
            }
        };
    }

    #[test]
    fn test_multiline_lexeme() {
        let src = "%%
'.*' 'STR'
[ \\n] ;"
            .to_string();
        let mut lexerdef = parse_lex(&src).unwrap();
        let mut map = HashMap::new();
        map.insert("STR", 0u8);
        assert_eq!(lexerdef.set_rule_ids(&map), (None, None));

        let lexer = lexerdef.lexer("'a\nb'\n");
        let lexemes = lexer.iter().map(|x| x.unwrap()).collect::<Vec<_>>();
        assert_eq!(lexemes.len(), 1);
        assert_eq!(lexer.line_col(lexemes[0].span()), ((1, 1), (2, 3)));
        assert_eq!(lexer.span_lines_str(lexemes[0].span()), "'a\nb'");
    }
}
