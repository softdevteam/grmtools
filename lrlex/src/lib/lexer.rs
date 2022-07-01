use std::{
    collections::{HashMap, HashSet},
    fmt,
    hash::Hash,
    marker::PhantomData,
    slice::Iter,
    str::FromStr,
};

use cfgrammar::{NewlineCache, Span};
use num_traits::{PrimInt, Unsigned};
use regex::{self, Regex, RegexBuilder};
use try_from::TryFrom;

use lrpar::{LexError, Lexeme, Lexer, NonStreamingLexer};

use crate::{parser::LexParser, parser::StartState, LexBuildResult};

#[derive(Debug)]
#[doc(hidden)]
pub struct Rule<StorageT> {
    /// If `Some`, the ID that lexemes created against this rule will be given (lrlex gives such
    /// rules a guaranteed unique value, though that value can be overridden by clients who need to
    /// control the ID). If `None`, then this rule specifies lexemes which should not appear in the
    /// user's input.
    pub(super) tok_id: Option<StorageT>,
    /// This rule's name. If None, then text which matches this rule will be skipped (i.e. will not
    /// create a lexeme).
    pub name: Option<String>,
    pub name_span: Span,
    pub(super) re_str: String,
    re: Regex,
    /// Id(s) of permitted start conditions for the lexer to match this rule.
    pub start_states: Vec<usize>,
    /// If Some(state), successful matching of this rule will cause the current start condition of
    /// the lexer to be changed to the enclosed value. If none, successful matching causes no change
    /// to the current start condition.
    pub target_state: Option<usize>,
}

impl<StorageT> Rule<StorageT> {
    /// Create a new `Rule`. This interface is unstable and should only be used by code generated
    /// by lrlex itself.
    #[doc(hidden)]
    pub fn new(
        tok_id: Option<StorageT>,
        name: Option<String>,
        name_span: Span,
        re_str: String,
        start_states: Vec<usize>,
        target_state: Option<usize>,
    ) -> Result<Rule<StorageT>, regex::Error> {
        let re = RegexBuilder::new(&format!("\\A(?:{})", re_str))
            .multi_line(true)
            .dot_matches_new_line(true)
            .build()?;
        Ok(Rule {
            tok_id,
            name,
            name_span,
            re_str,
            re,
            start_states,
            target_state,
        })
    }
}

/// Methods which all lexer definitions must implement.
pub trait LexerDef<StorageT> {
    #[doc(hidden)]
    /// Instantiate a lexer from a set of `Rule`s. This is only intended to be used by compiled
    /// lexers (see `ctbuilder.rs`).
    fn from_rules(start_states: Vec<StartState>, rules: Vec<Rule<StorageT>>) -> Self
    where
        Self: Sized;

    /// Instantiate a lexer from a string (e.g. representing a `.l` file).
    fn from_str(s: &str) -> LexBuildResult<Self>
    where
        Self: Sized;

    /// Get the `Rule` at index `idx`.
    fn get_rule(&self, idx: usize) -> Option<&Rule<StorageT>>;

    /// Get the `Rule` instance associated with a particular lexeme ID. Panics if no such rule
    /// exists.
    fn get_rule_by_id(&self, tok_id: StorageT) -> &Rule<StorageT>;

    /// Get the `Rule` instance associated with a particular name.
    fn get_rule_by_name(&self, n: &str) -> Option<&Rule<StorageT>>;

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
    fn set_rule_ids<'a>(
        &'a mut self,
        rule_ids_map: &HashMap<&'a str, StorageT>,
    ) -> (Option<HashSet<&'a str>>, Option<HashSet<&'a str>>);

    /// Returns an iterator over all rules in this AST.
    fn iter_rules(&self) -> Iter<Rule<StorageT>>;

    /// Returns an iterator over all start states in this AST.
    fn iter_start_states(&self) -> Iter<StartState>;
}

/// This struct represents, in essence, a .l file in memory. From it one can produce an
/// [LRNonStreamingLexer] which actually lexes inputs.
pub struct LRNonStreamingLexerDef<LexemeT, StorageT> {
    rules: Vec<Rule<StorageT>>,
    start_states: Vec<StartState>,
    phantom: PhantomData<LexemeT>,
}

impl<LexemeT, StorageT: Copy + Eq + Hash + PrimInt + TryFrom<usize> + Unsigned> LexerDef<StorageT>
    for LRNonStreamingLexerDef<LexemeT, StorageT>
{
    fn from_rules(
        start_states: Vec<StartState>,
        rules: Vec<Rule<StorageT>>,
    ) -> LRNonStreamingLexerDef<LexemeT, StorageT> {
        LRNonStreamingLexerDef {
            rules,
            start_states,
            phantom: PhantomData,
        }
    }

    fn from_str(s: &str) -> LexBuildResult<LRNonStreamingLexerDef<LexemeT, StorageT>> {
        LexParser::new(s.to_string()).map(|p| LRNonStreamingLexerDef {
            rules: p.rules,
            start_states: p.start_states,
            phantom: PhantomData,
        })
    }

    fn get_rule(&self, idx: usize) -> Option<&Rule<StorageT>> {
        self.rules.get(idx)
    }

    fn get_rule_by_id(&self, tok_id: StorageT) -> &Rule<StorageT> {
        self.rules
            .iter()
            .find(|r| r.tok_id == Some(tok_id))
            .unwrap()
    }

    fn get_rule_by_name(&self, n: &str) -> Option<&Rule<StorageT>> {
        self.rules.iter().find(|r| r.name.as_deref() == Some(n))
    }

    fn set_rule_ids<'a>(
        &'a mut self,
        rule_ids_map: &HashMap<&'a str, StorageT>,
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

        let missing_from_parser = if missing_from_parser_idxs.is_empty() {
            None
        } else {
            let mut mfp = HashSet::with_capacity(missing_from_parser_idxs.len());
            for i in &missing_from_parser_idxs {
                mfp.insert(self.rules[*i].name.as_ref().unwrap().as_str());
            }
            Some(mfp)
        };

        let missing_from_lexer =
            if rules_with_names - missing_from_parser_idxs.len() == rule_ids_map.len() {
                None
            } else {
                Some(
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
                                .collect::<HashSet<&str>>(),
                        )
                        .cloned()
                        .collect::<HashSet<&str>>(),
                )
            };

        (missing_from_lexer, missing_from_parser)
    }

    fn iter_rules(&self) -> Iter<Rule<StorageT>> {
        self.rules.iter()
    }

    fn iter_start_states(&self) -> Iter<StartState> {
        self.start_states.iter()
    }
}

impl<
        LexemeT: Lexeme<StorageT>,
        StorageT: Copy + Eq + fmt::Debug + Hash + PrimInt + TryFrom<usize> + Unsigned,
    > LRNonStreamingLexerDef<LexemeT, StorageT>
{
    /// Return an [LRNonStreamingLexer] for the `String` `s` that will lex relative to this
    /// [LRNonStreamingLexerDef].
    pub fn lexer<'lexer, 'input: 'lexer>(
        &'lexer self,
        s: &'input str,
    ) -> LRNonStreamingLexer<'lexer, 'input, LexemeT, StorageT> {
        let mut lexemes = vec![];
        let mut i = 0;
        let state = self.get_start_state_by_id(0);
        let mut state = match state {
            None => {
                lexemes.push(Err(LexError::new(Span::new(i, i))));
                return LRNonStreamingLexer::new(s, lexemes, NewlineCache::from_str(s).unwrap());
            }
            Some(state) => state,
        };
        while i < s.len() {
            let old_i = i;
            let mut longest = 0; // Length of the longest match
            let mut longest_ridx = 0; // This is only valid iff longest != 0
            for (ridx, r) in self.iter_rules().enumerate() {
                if !Self::state_matches(state, &r.start_states) {
                    continue;
                }
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
                let r = self.get_rule(longest_ridx).unwrap();
                if r.name.is_some() {
                    match r.tok_id {
                        Some(tok_id) => {
                            lexemes.push(Ok(Lexeme::new(tok_id, old_i, longest)));
                        }
                        None => {
                            lexemes.push(Err(LexError::new(Span::new(old_i, old_i))));
                            break;
                        }
                    }
                }
                if let Some(target_state_id) = r.target_state {
                    state = match self.get_start_state_by_id(target_state_id) {
                        None => {
                            lexemes.push(Err(LexError::new(Span::new(old_i, old_i))));
                            break;
                        }
                        Some(state) => state,
                    }
                }
                i += longest;
            } else {
                lexemes.push(Err(LexError::new(Span::new(old_i, old_i))));
                break;
            }
        }
        LRNonStreamingLexer::new(s, lexemes, NewlineCache::from_str(s).unwrap())
    }

    fn state_matches(state: &StartState, rule_states: &Vec<usize>) -> bool {
        if rule_states.is_empty() {
            !state.exclusive
        } else {
            rule_states.contains(&state.id)
        }
    }

    fn get_start_state_by_id(&self, id: usize) -> Option<&StartState> {
        self.start_states.iter().find(|state| state.id == id)
    }
}

/// An `LRNonStreamingLexer` holds a reference to a string and can lex it into [lrpar::Lexeme]s.
/// Although the struct is tied to a single string, no guarantees are made about whether the
/// lexemes are cached or not.
pub struct LRNonStreamingLexer<'lexer, 'input: 'lexer, LexemeT, StorageT: fmt::Debug> {
    s: &'input str,
    lexemes: Vec<Result<LexemeT, LexError>>,
    newlines: NewlineCache,
    phantom: PhantomData<(&'lexer (), StorageT)>,
}

impl<
        'lexer,
        'input: 'lexer,
        LexemeT: Lexeme<StorageT>,
        StorageT: Copy + Eq + fmt::Debug + Hash + PrimInt + TryFrom<usize> + Unsigned,
    > LRNonStreamingLexer<'lexer, 'input, LexemeT, StorageT>
{
    /// Create a new `LRNonStreamingLexer` that read in: the input `s`; and derived `lexemes` and
    /// `newlines`.
    ///
    /// Note that if one or more lexemes or newlines was not created from `s`, subsequent calls to
    /// the `LRNonStreamingLexer` may cause `panic`s.
    pub fn new(
        s: &'input str,
        lexemes: Vec<Result<LexemeT, LexError>>,
        newlines: NewlineCache,
    ) -> LRNonStreamingLexer<'lexer, 'input, LexemeT, StorageT> {
        LRNonStreamingLexer {
            s,
            lexemes,
            newlines,
            phantom: PhantomData,
        }
    }
}

impl<
        'lexer,
        'input: 'lexer,
        LexemeT: Lexeme<StorageT>,
        StorageT: Copy + fmt::Debug + Eq + Hash + PrimInt + Unsigned,
    > Lexer<LexemeT, StorageT> for LRNonStreamingLexer<'lexer, 'input, LexemeT, StorageT>
{
    fn iter<'a>(&'a self) -> Box<dyn Iterator<Item = Result<LexemeT, LexError>> + 'a> {
        Box::new(self.lexemes.iter().cloned())
    }
}

impl<
        'lexer,
        'input: 'lexer,
        LexemeT: Lexeme<StorageT>,
        StorageT: Copy + Eq + fmt::Debug + Hash + PrimInt + Unsigned,
    > NonStreamingLexer<'input, LexemeT, StorageT>
    for LRNonStreamingLexer<'lexer, 'input, LexemeT, StorageT>
{
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

        let (st, en) = self.newlines.span_line_bytes(span);
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

        (
            self.newlines
                .byte_to_line_num_and_col_num(self.s, span.start())
                .unwrap(),
            self.newlines
                .byte_to_line_num_and_col_num(self.s, span.end())
                .unwrap(),
        )
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::DefaultLexeme;
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
        let mut lexerdef = LRNonStreamingLexerDef::<DefaultLexeme<u8>, u8>::from_str(&src).unwrap();
        let mut map = HashMap::new();
        map.insert("int", 0);
        map.insert("id", 1);
        assert_eq!(lexerdef.set_rule_ids(&map), (None, None));

        let lexemes = lexerdef
            .lexer("abc 123")
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
        let lexerdef = LRNonStreamingLexerDef::<DefaultLexeme<u8>, u8>::from_str(&src).unwrap();
        match lexerdef.lexer("abc").iter().next().unwrap() {
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
        let mut lexerdef = LRNonStreamingLexerDef::from_str(&src).unwrap();
        let mut map = HashMap::new();
        map.insert("IF", 0);
        map.insert("ID", 1);
        assert_eq!(lexerdef.set_rule_ids(&map), (None, None));

        let lexemes = lexerdef
            .lexer("iff if")
            .iter()
            .map(|x| x.unwrap())
            .collect::<Vec<DefaultLexeme<u8>>>();
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
        let mut lexerdef = LRNonStreamingLexerDef::from_str(&src).unwrap();
        let mut map = HashMap::new();
        map.insert("ID", 0u8);
        assert_eq!(lexerdef.set_rule_ids(&map), (None, None));

        let lexer = lexerdef.lexer("a ❤ a");
        let lexemes = lexer
            .iter()
            .map(|x| x.unwrap())
            .collect::<Vec<DefaultLexeme<u8>>>();
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
        let mut lexerdef = LRNonStreamingLexerDef::from_str(&src).unwrap();
        let mut map = HashMap::new();
        map.insert("ID", 0u8);
        assert_eq!(lexerdef.set_rule_ids(&map), (None, None));

        let lexer = lexerdef.lexer("a b c");
        let lexemes = lexer
            .iter()
            .map(|x| x.unwrap())
            .collect::<Vec<DefaultLexeme<u8>>>();
        assert_eq!(lexemes.len(), 3);
        assert_eq!(lexer.line_col(lexemes[1].span()), ((1, 3), (1, 4)));
        assert_eq!(lexer.span_lines_str(lexemes[1].span()), "a b c");
        assert_eq!(lexer.span_lines_str(lexemes[2].span()), "a b c");

        let lexer = lexerdef.lexer("a b c\n");
        let lexemes = lexer.iter().map(|x| x.unwrap()).collect::<Vec<_>>();
        assert_eq!(lexemes.len(), 3);
        assert_eq!(lexer.line_col(lexemes[1].span()), ((1, 3), (1, 4)));
        assert_eq!(lexer.span_lines_str(lexemes[1].span()), "a b c");
        assert_eq!(lexer.span_lines_str(lexemes[2].span()), "a b c");

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

        let mut s = Vec::new();
        let mut offs = vec![0];
        for i in 0..71 {
            offs.push(offs[i] + i + 1);
            s.push(vec!["a"; i].join(" "));
        }
        let s = s.join("\n");
        let lexer = lexerdef.lexer(&s);
        let lexemes = lexer.iter().map(|x| x.unwrap()).collect::<Vec<_>>();
        assert_eq!(lexemes.len(), offs[70]);
        assert_eq!(lexer.span_lines_str(Span::new(0, 0)), "");
        assert_eq!(lexer.span_lines_str(Span::new(0, 2)), "\na");
        assert_eq!(lexer.span_lines_str(Span::new(0, 4)), "\na\na a");
        assert_eq!(lexer.span_lines_str(Span::new(0, 7)), "\na\na a\na a a");
        assert_eq!(lexer.span_lines_str(Span::new(4, 7)), "a a\na a a");
        assert_eq!(lexer.span_lines_str(lexemes[0].span()), "a");
        assert_eq!(lexer.span_lines_str(lexemes[1].span()), "a a");
        assert_eq!(lexer.span_lines_str(lexemes[3].span()), "a a a");
        for i in 0..70 {
            assert_eq!(
                lexer.span_lines_str(lexemes[offs[i]].span()),
                vec!["a"; i + 1].join(" ")
            );
        }
    }

    #[test]
    fn test_line_col_multibyte() {
        let src = "%%
[a-z❤]+ 'ID'
[ \\n] ;"
            .to_string();
        let mut lexerdef = LRNonStreamingLexerDef::from_str(&src).unwrap();
        let mut map = HashMap::new();
        map.insert("ID", 0u8);
        assert_eq!(lexerdef.set_rule_ids(&map), (None, None));

        let lexer = lexerdef.lexer(" a\n❤ b");
        let lexemes = lexer
            .iter()
            .map(|x| x.unwrap())
            .collect::<Vec<DefaultLexeme<u8>>>();
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
        let mut lexerdef = LRNonStreamingLexerDef::<DefaultLexeme<u8>, _>::from_str(&src).unwrap();
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
        let mut lexerdef = LRNonStreamingLexerDef::<DefaultLexeme<u8>, _>::from_str(&src).unwrap();
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

        match lexerdef.lexer(" a ").iter().next().unwrap() {
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
        let mut lexerdef = LRNonStreamingLexerDef::from_str(&src).unwrap();
        let mut map = HashMap::new();
        map.insert("STR", 0u8);
        assert_eq!(lexerdef.set_rule_ids(&map), (None, None));

        let lexer = lexerdef.lexer("'a\nb'\n");
        let lexemes = lexer
            .iter()
            .map(|x| x.unwrap())
            .collect::<Vec<DefaultLexeme<u8>>>();
        assert_eq!(lexemes.len(), 1);
        assert_eq!(lexer.line_col(lexemes[0].span()), ((1, 1), (2, 3)));
        assert_eq!(lexer.span_lines_str(lexemes[0].span()), "'a\nb'");
    }

    #[test]
    fn test_token_span() {
        let src = "%%
a 'A'
b 'B'
[ \\n] ;"
            .to_string();
        let lexerdef = LRNonStreamingLexerDef::<DefaultLexeme<u8>, u8>::from_str(&src).unwrap();
        assert_eq!(
            lexerdef.get_rule_by_name("A").unwrap().name_span,
            Span::new(6, 7)
        );
        assert_eq!(
            lexerdef.get_rule_by_name("B").unwrap().name_span,
            Span::new(12, 13)
        );
        let anonymous_rules = lexerdef
            .iter_rules()
            .filter(|rule| rule.name.is_none())
            .collect::<Vec<_>>();
        assert_eq!(anonymous_rules[0].name_span, Span::new(21, 21));
    }

    #[test]
    fn test_token_start_states() {
        let src = "%x EXCLUSIVE_START
%s INCLUSIVE_START
%%
a 'A'
b 'B'
[ \\n] ;"
            .to_string();
        let lexerdef = LRNonStreamingLexerDef::<DefaultLexeme<u8>, u8>::from_str(&src).unwrap();
        assert_eq!(
            lexerdef.get_rule_by_name("A").unwrap().name_span,
            Span::new(44, 45)
        );
        assert_eq!(
            lexerdef.get_rule_by_name("B").unwrap().name_span,
            Span::new(50, 51)
        );
    }

    #[test]
    fn test_rule_start_states() {
        let src = "%x EXCLUSIVE_START
%s INCLUSIVE_START
%%
<EXCLUSIVE_START>a 'A'
<INCLUSIVE_START>b 'B'
[ \\n] ;"
            .to_string();
        let lexerdef = LRNonStreamingLexerDef::<DefaultLexeme<u8>, u8>::from_str(&src).unwrap();
        let a_rule = lexerdef.get_rule_by_name("A").unwrap();
        assert_eq!(a_rule.name_span, Span::new(61, 62));
        assert_eq!(a_rule.re_str, "a");

        let b_rule = lexerdef.get_rule_by_name("B").unwrap();
        assert_eq!(b_rule.name_span, Span::new(84, 85));
        assert_eq!(b_rule.re_str, "b");
    }

    #[test]
    fn test_state_matches_regular_no_rule_states() {
        let all_states = &[
            StartState::new(0, "INITIAL", false),
            StartState::new(1, "EXCLUSIVE", true),
        ];
        let rule_states = vec![];
        let current_state = all_states.get(0).unwrap();
        let m = LRNonStreamingLexerDef::<DefaultLexeme<u8>, u8>::state_matches(
            current_state,
            &rule_states,
        );
        assert!(m);
    }

    #[test]
    fn test_state_matches_exclusive_no_rule_states() {
        let all_states = &[
            StartState::new(0, "INITIAL", false),
            StartState::new(1, "EXCLUSIVE", true),
        ];
        let rule_states = vec![];
        let current_state = all_states.get(1).unwrap();
        let m = LRNonStreamingLexerDef::<DefaultLexeme<u8>, u8>::state_matches(
            current_state,
            &rule_states,
        );
        assert!(!m);
    }

    #[test]
    fn test_state_matches_regular_matching_rule_states() {
        let all_states = &[
            StartState::new(0, "INITIAL", false),
            StartState::new(1, "EXCLUSIVE", true),
        ];
        let rule_states = vec![0];
        let current_state = all_states.get(0).unwrap();
        let m = LRNonStreamingLexerDef::<DefaultLexeme<u8>, u8>::state_matches(
            current_state,
            &rule_states,
        );
        assert!(m);
    }

    #[test]
    fn test_state_matches_exclusive_matching_rule_states() {
        let all_states = &[
            StartState::new(0, "INITIAL", false),
            StartState::new(1, "EXCLUSIVE", true),
        ];
        let rule_states = vec![1];
        let current_state = all_states.get(1).unwrap();
        let m = LRNonStreamingLexerDef::<DefaultLexeme<u8>, u8>::state_matches(
            current_state,
            &rule_states,
        );
        assert!(m);
    }

    #[test]
    fn test_state_matches_regular_other_rule_states() {
        let all_states = &[
            StartState::new(0, "INITIAL", false),
            StartState::new(1, "EXCLUSIVE", true),
        ];
        let rule_states = vec![1];
        let current_state = all_states.get(0).unwrap();
        let m = LRNonStreamingLexerDef::<DefaultLexeme<u8>, u8>::state_matches(
            current_state,
            &rule_states,
        );
        assert!(!m);
    }

    #[test]
    fn test_state_matches_exclusive_other_rule_states() {
        let all_states = &[
            StartState::new(0, "INITIAL", false),
            StartState::new(1, "EXCLUSIVE", true),
        ];
        let rule_states = vec![0];
        let current_state = all_states.get(1).unwrap();
        let m = LRNonStreamingLexerDef::<DefaultLexeme<u8>, u8>::state_matches(
            current_state,
            &rule_states,
        );
        assert!(!m);
    }
}
