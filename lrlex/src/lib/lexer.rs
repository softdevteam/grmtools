use std::{
    collections::{HashMap, HashSet},
    fmt::Debug,
    hash::Hash,
    marker::PhantomData,
    slice::Iter,
    str::FromStr,
};

use cfgrammar::{
    NewlineCache, Span,
    header::{GrmtoolsSectionParser, Header, HeaderError, HeaderErrorKind, HeaderValue, Value},
    span::Location,
};
use num_traits::{AsPrimitive, PrimInt, Unsigned};
use regex::{Regex, RegexBuilder};

use lrpar::{Lexeme, Lexer, LexerTypes, NonStreamingLexer};

use crate::{
    LRLexError, LexBuildError, LexBuildResult, StartStateId,
    parser::{LexParser, StartState, StartStateOperation},
};

#[doc(hidden)]
/// Corresponds to the options for `regex::RegexBuilder`.
#[derive(Clone, Debug)]
#[non_exhaustive]
pub struct LexFlags {
    // The following values when `None` grmtools provides default values for in `DEFAULT_LEX_FLAGS`
    pub dot_matches_new_line: Option<bool>,
    pub multi_line: Option<bool>,
    pub octal: Option<bool>,
    pub posix_escapes: Option<bool>,
    pub allow_wholeline_comments: Option<bool>,

    // All the following values when `None` default to the `regex` crate's default value.
    pub case_insensitive: Option<bool>,
    pub swap_greed: Option<bool>,
    pub ignore_whitespace: Option<bool>,
    pub unicode: Option<bool>,
    pub size_limit: Option<usize>,
    pub dfa_size_limit: Option<usize>,
    pub nest_limit: Option<u32>,
}

impl<T: Clone> TryFrom<&mut Header<T>> for LexFlags {
    type Error = HeaderError<T>;
    fn try_from(header: &mut Header<T>) -> Result<LexFlags, HeaderError<T>> {
        use cfgrammar::header::Setting;
        let mut lex_flags = UNSPECIFIED_LEX_FLAGS;
        let LexFlags {
            dot_matches_new_line,
            multi_line,
            octal,
            posix_escapes,
            allow_wholeline_comments,
            case_insensitive,
            swap_greed,
            ignore_whitespace,
            unicode,
            size_limit,
            dfa_size_limit,
            nest_limit,
        } = &mut lex_flags;
        macro_rules! cvt_flag {
            ($it:ident) => {
                header.mark_used(&stringify!($it).to_string());
                *$it = match header.get(stringify!($it)) {
                    Some(HeaderValue(_, Value::Flag(flag, _))) => Some(*flag),
                    Some(HeaderValue(loc, _)) => Err(HeaderError {
                        kind: HeaderErrorKind::ConversionError("LexFlags", "Expected boolean"),
                        locations: vec![loc.clone()],
                    })?,
                    None => None,
                }
            };
        }
        cvt_flag!(dot_matches_new_line);
        cvt_flag!(multi_line);
        cvt_flag!(octal);
        cvt_flag!(posix_escapes);
        cvt_flag!(allow_wholeline_comments);
        cvt_flag!(case_insensitive);
        cvt_flag!(swap_greed);
        cvt_flag!(ignore_whitespace);
        cvt_flag!(unicode);
        macro_rules! cvt_num {
            ($it:ident, $num_ty: ty) => {
                header.mark_used(&stringify!($it).to_string());
                *$it = match header.get(stringify!($it)) {
                    Some(HeaderValue(_, Value::Setting(Setting::Num(n, _)))) => Some(*n as $num_ty),
                    Some(HeaderValue(loc, _)) => Err(HeaderError {
                        kind: HeaderErrorKind::ConversionError("LexFlags", "Expected numeric"),
                        locations: vec![loc.clone()],
                    })?,
                    None => None,
                }
            };
        }
        cvt_num!(size_limit, usize);
        cvt_num!(dfa_size_limit, usize);
        cvt_num!(nest_limit, u32);
        Ok(lex_flags)
    }
}

impl From<&LexFlags> for Header<Location> {
    fn from(flags: &LexFlags) -> Header<Location> {
        let mut header = Header::new();
        let LexFlags {
            dot_matches_new_line,
            multi_line,
            octal,
            posix_escapes,
            allow_wholeline_comments,
            case_insensitive,
            swap_greed,
            ignore_whitespace,
            unicode,
            size_limit,
            dfa_size_limit,
            nest_limit,
        } = flags;
        macro_rules! cvt_flag {
            ($it: ident) => {
                $it.map(|x| {
                    header.insert(
                        stringify!($it).to_string(),
                        HeaderValue(
                            Location::Other("From<&LexFlags".to_string()),
                            Value::Flag(x, Location::Other("From<&LexFlags>".to_string())),
                        ),
                    )
                });
            };
        }
        cvt_flag!(dot_matches_new_line);
        cvt_flag!(multi_line);
        cvt_flag!(octal);
        cvt_flag!(posix_escapes);
        cvt_flag!(allow_wholeline_comments);
        cvt_flag!(case_insensitive);
        cvt_flag!(swap_greed);
        cvt_flag!(ignore_whitespace);
        cvt_flag!(unicode);

        macro_rules! cvt_num {
            ($it: ident) => {
                $it.map(|x| {
                    use cfgrammar::header::Setting;
                    header.insert(
                        stringify!($it).to_string(),
                        HeaderValue(
                            Location::Other("From<&LexFlags".to_string()),
                            Value::Setting(Setting::Num(
                                x as u64,
                                Location::Other("From<&LexFlags>".to_string()),
                            )),
                        ),
                    )
                });
            };
        }
        cvt_num!(size_limit);
        cvt_num!(dfa_size_limit);
        cvt_num!(nest_limit);

        header
    }
}

/// LexFlags with flags set to default values.
#[doc(hidden)]
pub const DEFAULT_LEX_FLAGS: LexFlags = LexFlags {
    allow_wholeline_comments: Some(false),
    dot_matches_new_line: Some(true),
    multi_line: Some(true),
    octal: Some(true),
    posix_escapes: Some(false),
    case_insensitive: None,
    ignore_whitespace: None,
    swap_greed: None,
    unicode: None,
    size_limit: None,
    dfa_size_limit: None,
    nest_limit: None,
};

#[doc(hidden)]
/// LexFlags with all of the values `None`.
pub const UNSPECIFIED_LEX_FLAGS: LexFlags = LexFlags {
    allow_wholeline_comments: None,
    dot_matches_new_line: None,
    multi_line: None,
    octal: None,
    posix_escapes: None,
    case_insensitive: None,
    ignore_whitespace: None,
    swap_greed: None,
    unicode: None,
    size_limit: None,
    dfa_size_limit: None,
    nest_limit: None,
};

#[derive(Debug, Clone)]
#[doc(hidden)]
pub struct Rule<StorageT> {
    /// If `Some`, this specifies the ID that lexemes resulting from this rule will have. Note that
    /// lrlex gives rules a guaranteed unique value by default, though users can later override
    /// that, potentially undermining uniqueness if they're not careful.
    ///
    /// If `None`, then this rule specifies lexemes which should not appear in the user's input.
    pub(super) tok_id: Option<StorageT>,
    /// This rule's name. If None, then text which matches this rule will be skipped (i.e. will not
    /// create a lexeme).
    #[deprecated(note = "Use the name() function")]
    pub name: Option<String>,
    #[deprecated(note = "Use the name_span() function")]
    pub name_span: Span,
    pub(super) re_str: String,
    re: Regex,
    /// Id(s) of permitted start conditions for the lexer to match this rule.
    #[deprecated(note = "Use the start_states() function")]
    pub start_states: Vec<usize>,
    /// If Some(_), successful matching of this rule will cause the current stack of start
    /// conditions in the lexer to be updated with the enclosed value, using the designated
    /// operation.
    /// If None, successful matching causes no change to the current start condition.
    #[deprecated(note = "Use the target_state() function")]
    pub target_state: Option<(usize, StartStateOperation)>,
}

impl<StorageT: PrimInt> Rule<StorageT> {
    /// Create a new `Rule`. This interface is unstable and should only be used by code generated
    /// by lrlex itself.
    #[doc(hidden)]
    #[allow(private_interfaces)]
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        _: crate::unstable_api::InternalPublicApi,
        tok_id: Option<StorageT>,
        name: Option<String>,
        name_span: Span,
        re_str: String,
        start_states: Vec<usize>,
        target_state: Option<(usize, StartStateOperation)>,
        lex_flags: &LexFlags,
    ) -> Result<Rule<StorageT>, regex::Error> {
        let mut re = RegexBuilder::new(&format!("\\A(?:{})", re_str));
        let mut re = re
            .octal(lex_flags.octal.unwrap())
            .multi_line(lex_flags.multi_line.unwrap())
            .dot_matches_new_line(lex_flags.dot_matches_new_line.unwrap());

        if let Some(flag) = lex_flags.ignore_whitespace {
            re = re.ignore_whitespace(flag)
        }
        if let Some(flag) = lex_flags.unicode {
            re = re.unicode(flag)
        }
        if let Some(flag) = lex_flags.case_insensitive {
            re = re.case_insensitive(flag)
        }
        if let Some(flag) = lex_flags.swap_greed {
            re = re.swap_greed(flag)
        }
        if let Some(sz) = lex_flags.size_limit {
            re = re.size_limit(sz)
        }
        if let Some(sz) = lex_flags.dfa_size_limit {
            re = re.dfa_size_limit(sz)
        }
        if let Some(lim) = lex_flags.nest_limit {
            re = re.nest_limit(lim)
        }

        let re = re.build()?;
        #[allow(deprecated)]
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

    /// Return this rule's token ID, if any.
    ///
    /// If `Some`, this specifies the ID that lexemes resulting from this rule will have. If
    /// `None`, then this rule specifies lexemes which should not appear in the user's input.
    pub fn tok_id(&self) -> Option<StorageT> {
        self.tok_id
    }

    /// Return this rule's name. If `None`, then text which matches this rule will be skipped (i.e.
    /// it will not result in the creation of a [Lexeme]).
    pub fn name(&self) -> Option<&str> {
        #[allow(deprecated)]
        self.name.as_deref()
    }

    /// Return the [Span] of this rule's name.
    pub fn name_span(&self) -> Span {
        #[allow(deprecated)]
        self.name_span
    }

    /// Return the original regular expression specified by the user for this [Rule].
    pub fn re_str(&self) -> &str {
        &self.re_str
    }

    /// Return the IDs of the permitted start conditions for the lexer to match this rule.
    pub fn start_states(&self) -> &[usize] {
        #[allow(deprecated)]
        self.start_states.as_slice()
    }

    /// Return the IDs of the permitted start conditions for the lexer to match this rule.
    pub fn target_state(&self) -> Option<(usize, StartStateOperation)> {
        #[allow(deprecated)]
        self.target_state.clone()
    }
}

/// Methods which all lexer definitions must implement.
pub trait LexerDef<LexerTypesT: LexerTypes>
where
    usize: AsPrimitive<LexerTypesT::StorageT>,
{
    #[doc(hidden)]
    /// Instantiate a lexer from a set of `Rule`s. This is only intended to be used by compiled
    /// lexers (see `ctbuilder.rs`).
    fn from_rules(start_states: Vec<StartState>, rules: Vec<Rule<LexerTypesT::StorageT>>) -> Self
    where
        Self: Sized;

    /// Instantiate a lexer from a string (e.g. representing a `.l` file).
    fn from_str(s: &str) -> LexBuildResult<Self>
    where
        Self: Sized;

    /// Get the `Rule` at index `idx`.
    fn get_rule(&self, idx: usize) -> Option<&Rule<LexerTypesT::StorageT>>;

    /// Get the `Rule` instance associated with a particular lexeme ID. Panics if no such rule
    /// exists.
    fn get_rule_by_id(&self, tok_id: LexerTypesT::StorageT) -> &Rule<LexerTypesT::StorageT>;

    /// Get the `Rule` instance associated with a particular name.
    fn get_rule_by_name(&self, n: &str) -> Option<&Rule<LexerTypesT::StorageT>>;

    /// Set the id attribute on rules to the corresponding value in `map`. This is typically used
    /// to synchronise a parser's notion of lexeme IDs with the lexers. While doing this, it keeps
    /// track of which lexemes:
    ///   1) are defined in the lexer but not referenced by the parser
    ///   2) and referenced by the parser but not defined in the lexer
    ///
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
        rule_ids_map: &HashMap<&'a str, LexerTypesT::StorageT>,
    ) -> (Option<HashSet<&'a str>>, Option<HashSet<&'a str>>);

    fn set_rule_ids_spanned<'a>(
        &'a mut self,
        rule_ids_map: &HashMap<&'a str, LexerTypesT::StorageT>,
    ) -> (Option<HashSet<&'a str>>, Option<HashSet<(&'a str, Span)>>);

    /// Returns an iterator over all rules in this AST.
    fn iter_rules(&self) -> Iter<'_, Rule<LexerTypesT::StorageT>>;

    /// Returns an iterator over all start states in this AST.
    fn iter_start_states(&self) -> Iter<'_, StartState>;
}

/// This struct represents, in essence, a .l file in memory. From it one can produce an
/// [LRNonStreamingLexer] which actually lexes inputs.
#[derive(Debug, Clone)]
pub struct LRNonStreamingLexerDef<LexerTypesT: LexerTypes>
where
    usize: AsPrimitive<LexerTypesT::StorageT>,
{
    rules: Vec<Rule<LexerTypesT::StorageT>>,
    start_states: Vec<StartState>,
    lex_flags: LexFlags,
    phantom: PhantomData<LexerTypesT>,
}

impl<LexerTypesT: LexerTypes> LexerDef<LexerTypesT> for LRNonStreamingLexerDef<LexerTypesT>
where
    usize: AsPrimitive<LexerTypesT::StorageT>,
    LexerTypesT::StorageT: TryFrom<usize>,
{
    fn from_rules(
        start_states: Vec<StartState>,
        rules: Vec<Rule<LexerTypesT::StorageT>>,
    ) -> LRNonStreamingLexerDef<LexerTypesT> {
        LRNonStreamingLexerDef {
            rules,
            start_states,
            lex_flags: DEFAULT_LEX_FLAGS,
            phantom: PhantomData,
        }
    }

    /// Given a `.l` file in an `&str`, returns a `LrNonStreamingLexerDef`
    /// after merging the `%grmtools` section with the default set of `LexFlags`.
    fn from_str(s: &str) -> LexBuildResult<LRNonStreamingLexerDef<LexerTypesT>> {
        let (mut header, pos) = GrmtoolsSectionParser::new(s, false)
            .parse()
            .map_err(|mut errs| errs.drain(..).map(LexBuildError::from).collect::<Vec<_>>())?;
        let flags = LexFlags::try_from(&mut header).map_err(|e| vec![e.into()])?;
        LexParser::<LexerTypesT>::new_with_lex_flags(s[pos..].to_string(), flags.clone()).map(|p| {
            LRNonStreamingLexerDef {
                rules: p.rules,
                start_states: p.start_states,
                lex_flags: flags,
                phantom: PhantomData,
            }
        })
    }

    fn get_rule(&self, idx: usize) -> Option<&Rule<LexerTypesT::StorageT>> {
        self.rules.get(idx)
    }

    fn get_rule_by_id(&self, tok_id: LexerTypesT::StorageT) -> &Rule<LexerTypesT::StorageT> {
        self.rules
            .iter()
            .find(|r| r.tok_id == Some(tok_id))
            .unwrap()
    }

    fn get_rule_by_name(&self, n: &str) -> Option<&Rule<LexerTypesT::StorageT>> {
        self.rules.iter().find(|r| r.name() == Some(n))
    }

    fn set_rule_ids<'a>(
        &'a mut self,
        rule_ids_map: &HashMap<&'a str, LexerTypesT::StorageT>,
    ) -> (Option<HashSet<&'a str>>, Option<HashSet<&'a str>>) {
        let (missing_from_parser, missing_from_lexer) = self.set_rule_ids_spanned(rule_ids_map);
        let missing_from_lexer =
            missing_from_lexer.map(|missing| missing.iter().map(|(name, _)| *name).collect());
        (missing_from_parser, missing_from_lexer)
    }

    fn set_rule_ids_spanned<'a>(
        &'a mut self,
        rule_ids_map: &HashMap<&'a str, LexerTypesT::StorageT>,
    ) -> (Option<HashSet<&'a str>>, Option<HashSet<(&'a str, Span)>>) {
        // Because we have to iter_mut over self.rules, we can't easily store a reference to the
        // rule's name at the same time. Instead, we store the index of each such rule and
        // recover the names later. This has the unfortunate consequence of extended the mutable
        // borrow for the rest of the 'a lifetime. To avoid that we could return idx's here.
        // But the original `set_rule_ids` invalidates indexes.  In the spirit of keeping that
        // behavior consistent, this also returns the span.
        let mut missing_from_parser_idxs = Vec::new();
        let mut rules_with_names = 0;
        for (i, r) in self.rules.iter_mut().enumerate() {
            if let Some(n) = r.name() {
                match rule_ids_map.get(n) {
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
                mfp.insert((self.rules[*i].name().unwrap(), self.rules[*i].name_span()));
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
                                .filter_map(|x| x.name())
                                .collect::<HashSet<&str>>(),
                        )
                        .cloned()
                        .collect::<HashSet<&str>>(),
                )
            };

        (missing_from_lexer, missing_from_parser)
    }

    fn iter_rules(&self) -> Iter<'_, Rule<LexerTypesT::StorageT>> {
        self.rules.iter()
    }

    fn iter_start_states(&self) -> Iter<'_, StartState> {
        self.start_states.iter()
    }
}

impl<
    StorageT: 'static + Debug + Hash + PrimInt + Unsigned,
    LexerTypesT: LexerTypes<StorageT = StorageT>,
> LRNonStreamingLexerDef<LexerTypesT>
where
    usize: AsPrimitive<StorageT>,
    LexerTypesT::StorageT: TryFrom<usize>,
{
    /// Uses the `lex_flags` passed in ignoring any settings in the `%grmtools` section.
    pub fn new_with_options(
        s: &str,
        lex_flags: LexFlags,
    ) -> LexBuildResult<LRNonStreamingLexerDef<LexerTypesT>> {
        let (_, pos) = GrmtoolsSectionParser::new(s, false).parse().unwrap();
        LexParser::<LexerTypesT>::new_with_lex_flags(s[pos..].to_string(), lex_flags.clone()).map(
            |p| LRNonStreamingLexerDef {
                rules: p.rules,
                start_states: p.start_states,
                lex_flags,
                phantom: PhantomData,
            },
        )
    }

    /// Return an [LRNonStreamingLexer] for the `String` `s` that will lex relative to this
    /// [LRNonStreamingLexerDef].
    pub fn lexer<'lexer, 'input: 'lexer>(
        &'lexer self,
        s: &'input str,
    ) -> LRNonStreamingLexer<'lexer, 'input, LexerTypesT> {
        let mut lexemes = vec![];
        let mut i = 0;
        let mut state_stack: Vec<(usize, &StartState)> = Vec::new();
        let initial_state = match self.get_start_state_by_id(0) {
            None => {
                lexemes.push(Err(LRLexError::new(Span::new(i, i))));
                return LRNonStreamingLexer::new(s, lexemes, NewlineCache::from_str(s).unwrap());
            }
            Some(state) => state,
        };
        state_stack.push((1, initial_state));

        while i < s.len() {
            let old_i = i;
            let mut longest = 0; // Length of the longest match
            let mut longest_ridx = 0; // This is only valid iff longest != 0
            let current_state = match state_stack.last() {
                None => {
                    lexemes.push(Err(LRLexError::new(Span::new(i, i))));
                    return LRNonStreamingLexer::new(
                        s,
                        lexemes,
                        NewlineCache::from_str(s).unwrap(),
                    );
                }
                Some((_, s)) => s,
            };
            for (ridx, r) in self.iter_rules().enumerate() {
                if !Self::state_matches(current_state, r.start_states()) {
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
                if r.name().is_some() {
                    match r.tok_id {
                        Some(tok_id) => {
                            lexemes.push(Ok(Lexeme::new(tok_id, old_i, longest)));
                        }
                        None => {
                            lexemes.push(Err(LRLexError::new(Span::new(old_i, old_i))));
                            break;
                        }
                    }
                }
                if let Some((target_state_id, op)) = &r.target_state() {
                    let state = match self.get_start_state_by_id(*target_state_id) {
                        None => {
                            // TODO: I can see an argument for lexing state to be either `None` or `Some(target_state_id)` here
                            lexemes.push(Err(LRLexError::new(Span::new(old_i, old_i))));
                            break;
                        }
                        Some(state) => state,
                    };
                    let head = state_stack.last_mut();
                    match op {
                        StartStateOperation::ReplaceStack => {
                            state_stack.clear();
                            state_stack.push((1, state));
                        }
                        StartStateOperation::Push => match head {
                            Some((count, s)) if s.id == state.id => *count += 1,
                            _ => state_stack.push((1, state)),
                        },
                        StartStateOperation::Pop => match head {
                            Some((count, _s)) if *count > 1 => {
                                *count -= 1;
                            }
                            Some(_) => {
                                state_stack.pop();
                                if state_stack.is_empty() {
                                    state_stack.push((1, initial_state));
                                }
                            }
                            None => {
                                lexemes.push(Err(LRLexError::new(Span::new(old_i, old_i))));
                                break;
                            }
                        },
                    }
                }
                i += longest;
            } else {
                lexemes.push(Err(LRLexError::new_with_lexing_state(
                    Span::new(old_i, old_i),
                    StartStateId::new(current_state.id),
                )));
                break;
            }
        }
        LRNonStreamingLexer::new(s, lexemes, NewlineCache::from_str(s).unwrap())
    }

    fn state_matches(state: &StartState, rule_states: &[usize]) -> bool {
        if rule_states.is_empty() {
            !state.exclusive
        } else {
            rule_states.contains(&state.id)
        }
    }

    fn get_start_state_by_id(&self, id: usize) -> Option<&StartState> {
        self.start_states.iter().find(|state| state.id == id)
    }

    /// Returns the final `LexFlags` used for this lex source
    /// after all forced and default flags have been resolved.
    pub(crate) fn lex_flags(&self) -> Option<&LexFlags> {
        Some(&self.lex_flags)
    }
}

/// An `LRNonStreamingLexer` holds a reference to a string and can lex it into [lrpar::Lexeme]s.
/// Although the struct is tied to a single string, no guarantees are made about whether the
/// lexemes are cached or not.
pub struct LRNonStreamingLexer<'lexer, 'input: 'lexer, LexerTypesT: LexerTypes>
where
    usize: AsPrimitive<LexerTypesT::StorageT>,
    LexerTypesT::StorageT: 'static + Debug + PrimInt,
{
    s: &'input str,
    lexemes: Vec<Result<LexerTypesT::LexemeT, LRLexError>>,
    newlines: NewlineCache,
    phantom: PhantomData<(&'lexer (), LexerTypesT::StorageT)>,
}

impl<
    'lexer,
    'input: 'lexer,
    StorageT: 'static + Debug + Hash + PrimInt + Unsigned,
    LexerTypesT: LexerTypes<StorageT = StorageT>,
> LRNonStreamingLexer<'lexer, 'input, LexerTypesT>
where
    usize: AsPrimitive<StorageT>,
{
    /// Create a new `LRNonStreamingLexer` that read in: the input `s`; and derived `lexemes` and
    /// `newlines`.
    ///
    /// Note that if one or more lexemes or newlines was not created from `s`, subsequent calls to
    /// the `LRNonStreamingLexer` may cause `panic`s.
    pub fn new(
        s: &'input str,
        lexemes: Vec<Result<LexerTypesT::LexemeT, LRLexError>>,
        newlines: NewlineCache,
    ) -> LRNonStreamingLexer<'lexer, 'input, LexerTypesT> {
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
    StorageT: 'static + Debug + Hash + PrimInt + Unsigned,
    LexerTypesT: LexerTypes<StorageT = StorageT, LexErrorT = LRLexError>,
> Lexer<LexerTypesT> for LRNonStreamingLexer<'lexer, 'input, LexerTypesT>
where
    usize: AsPrimitive<StorageT>,
{
    fn iter<'a>(
        &'a self,
    ) -> Box<dyn Iterator<Item = Result<LexerTypesT::LexemeT, LexerTypesT::LexErrorT>> + 'a> {
        Box::new(self.lexemes.iter().cloned())
    }
}

impl<'lexer, 'input: 'lexer, LexerTypesT: LexerTypes<LexErrorT = LRLexError>>
    NonStreamingLexer<'input, LexerTypesT> for LRNonStreamingLexer<'lexer, 'input, LexerTypesT>
where
    usize: AsPrimitive<LexerTypesT::StorageT>,
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
    use crate::{DefaultLexeme, DefaultLexerTypes};
    use lrpar::LexError;
    use std::collections::HashMap;

    #[test]
    fn test_basic() {
        let src = r"
%%
[0-9]+ 'int'
[a-zA-Z]+ 'id'
[ \t] ;"
            .to_string();
        let mut lexerdef = LRNonStreamingLexerDef::<DefaultLexerTypes<u8>>::from_str(&src).unwrap();
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
    fn test_posix_escapes() {
        let src = r#"%%
\\ 'slash'
\a 'alert'
\b 'backspace'
\f 'feed'
\n 'newline'
\r 'return'
\t 'tab'
\v 'vtab'
\q 'normal_char'
"#
        .to_string();
        let mut options = DEFAULT_LEX_FLAGS;
        options.posix_escapes = Some(true);
        let lexerdef =
            LRNonStreamingLexerDef::<DefaultLexerTypes<u8>>::new_with_options(&src, options)
                .unwrap();
        let lexemes = lexerdef
            .lexer("\\\x07\x08\x0c\n\r\t\x0bq")
            .iter()
            .map(|x| x.unwrap())
            .collect::<Vec<_>>();
        assert_eq!(lexemes.len(), 9);
        for i in 0..9u8 {
            let lexeme = lexemes[i as usize];
            assert_eq!(lexeme.tok_id(), i);
        }
    }

    #[test]
    fn test_non_posix_escapes() {
        let src = r#"%%
\\ 'slash'
\a 'alert'
a\b a 'work_break'
\f 'feed'
\n 'newline'
\r 'return'
\t 'tab'
\v 'vtab'
\q 'normal_char'
"#
        .to_string();
        let mut options = DEFAULT_LEX_FLAGS;
        options.posix_escapes = Some(false);
        let lexerdef =
            LRNonStreamingLexerDef::<DefaultLexerTypes<u8>>::new_with_options(&src, options)
                .unwrap();
        let lexemes = lexerdef
            .lexer("\\\x07a a\x0c\n\r\t\x0bq")
            .iter()
            .map(|x| x.unwrap())
            .collect::<Vec<_>>();
        assert_eq!(lexemes.len(), 9);
        for i in 0..9u8 {
            let lexeme = lexemes[i as usize];
            assert_eq!(lexeme.tok_id(), i);
        }
    }

    #[test]
    fn test_basic_error() {
        let src = "
%%
[0-9]+ 'int'"
            .to_string();
        let lexerdef = LRNonStreamingLexerDef::<DefaultLexerTypes<u8>>::from_str(&src).unwrap();
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
        let mut lexerdef = LRNonStreamingLexerDef::<DefaultLexerTypes<u8>>::from_str(&src).unwrap();
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
        let mut lexerdef = LRNonStreamingLexerDef::<DefaultLexerTypes<u8>>::from_str(&src).unwrap();
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
        let mut lexerdef = LRNonStreamingLexerDef::<DefaultLexerTypes<u8>>::from_str(&src).unwrap();
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
        let mut lexerdef = LRNonStreamingLexerDef::<DefaultLexerTypes<u8>>::from_str(&src).unwrap();
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
        let mut lexerdef = LRNonStreamingLexerDef::<DefaultLexerTypes<u8>>::from_str(&src).unwrap();
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
        let mut lexerdef = LRNonStreamingLexerDef::<DefaultLexerTypes<u8>>::from_str(&src).unwrap();
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
        let mut lexerdef = LRNonStreamingLexerDef::<DefaultLexerTypes<u8>>::from_str(&src).unwrap();
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
        let lexerdef = LRNonStreamingLexerDef::<DefaultLexerTypes<u8>>::from_str(&src).unwrap();
        assert_eq!(
            lexerdef.get_rule_by_name("A").unwrap().name_span(),
            Span::new(6, 7)
        );
        assert_eq!(
            lexerdef.get_rule_by_name("B").unwrap().name_span(),
            Span::new(12, 13)
        );
        let anonymous_rules = lexerdef
            .iter_rules()
            .filter(|rule| rule.name().is_none())
            .collect::<Vec<_>>();
        assert_eq!(anonymous_rules[0].name_span(), Span::new(21, 21));
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
        let lexerdef = LRNonStreamingLexerDef::<DefaultLexerTypes<u8>>::from_str(&src).unwrap();
        assert_eq!(
            lexerdef.get_rule_by_name("A").unwrap().name_span(),
            Span::new(44, 45)
        );
        assert_eq!(
            lexerdef.get_rule_by_name("B").unwrap().name_span(),
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
        let lexerdef = LRNonStreamingLexerDef::<DefaultLexerTypes<u8>>::from_str(&src).unwrap();
        let a_rule = lexerdef.get_rule_by_name("A").unwrap();
        assert_eq!(a_rule.name_span(), Span::new(61, 62));
        assert_eq!(a_rule.re_str, "a");

        let b_rule = lexerdef.get_rule_by_name("B").unwrap();
        assert_eq!(b_rule.name_span(), Span::new(84, 85));
        assert_eq!(b_rule.re_str, "b");
    }

    #[test]
    fn test_state_matches_regular_no_rule_states() {
        let all_states = &[
            StartState::new(0, "INITIAL", false, Span::new(0, 0)),
            StartState::new(1, "EXCLUSIVE", true, Span::new(0, 0)),
        ];
        let rule_states = vec![];
        let current_state = &all_states[0];
        let m = LRNonStreamingLexerDef::<DefaultLexerTypes<u8>>::state_matches(
            current_state,
            &rule_states,
        );
        assert!(m);
    }

    #[test]
    fn test_state_matches_exclusive_no_rule_states() {
        let all_states = &[
            StartState::new(0, "INITIAL", false, Span::new(0, 0)),
            StartState::new(1, "EXCLUSIVE", true, Span::new(0, 0)),
        ];
        let rule_states = vec![];
        let current_state = &all_states[1];
        let m = LRNonStreamingLexerDef::<DefaultLexerTypes<u8>>::state_matches(
            current_state,
            &rule_states,
        );
        assert!(!m);
    }

    #[test]
    fn test_state_matches_regular_matching_rule_states() {
        let all_states = &[
            StartState::new(0, "INITIAL", false, Span::new(0, 0)),
            StartState::new(1, "EXCLUSIVE", true, Span::new(0, 0)),
        ];
        let rule_states = vec![0];
        let current_state = &all_states[0];
        let m = LRNonStreamingLexerDef::<DefaultLexerTypes<u8>>::state_matches(
            current_state,
            &rule_states,
        );
        assert!(m);
    }

    #[test]
    fn test_state_matches_exclusive_matching_rule_states() {
        let all_states = &[
            StartState::new(0, "INITIAL", false, Span::new(0, 0)),
            StartState::new(1, "EXCLUSIVE", true, Span::new(0, 0)),
        ];
        let rule_states = vec![1];
        let current_state = &all_states[1];
        let m = LRNonStreamingLexerDef::<DefaultLexerTypes<u8>>::state_matches(
            current_state,
            &rule_states,
        );
        assert!(m);
    }

    #[test]
    fn test_state_matches_regular_other_rule_states() {
        let all_states = &[
            StartState::new(0, "INITIAL", false, Span::new(0, 0)),
            StartState::new(1, "EXCLUSIVE", true, Span::new(0, 0)),
        ];
        let rule_states = vec![1];
        let current_state = &all_states[0];
        let m = LRNonStreamingLexerDef::<DefaultLexerTypes<u8>>::state_matches(
            current_state,
            &rule_states,
        );
        assert!(!m);
    }

    #[test]
    fn test_state_matches_exclusive_other_rule_states() {
        let all_states = &[
            StartState::new(0, "INITIAL", false, Span::new(0, 0)),
            StartState::new(1, "EXCLUSIVE", true, Span::new(0, 0)),
        ];
        let rule_states = vec![0];
        let current_state = &all_states[1];
        let m = LRNonStreamingLexerDef::<DefaultLexerTypes<u8>>::state_matches(
            current_state,
            &rule_states,
        );
        assert!(!m);
    }
}
