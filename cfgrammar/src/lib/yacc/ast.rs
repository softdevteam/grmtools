use std::{
    collections::{HashMap, HashSet},
    error::Error,
    fmt,
    str::FromStr,
};

use indexmap::{IndexMap, IndexSet};

use super::{
    Precedence, YaccGrammarError, YaccGrammarErrorKind, YaccGrammarWarning, YaccGrammarWarningKind,
    YaccKind, parser::YaccParser,
};

use crate::{
    Span,
    header::{GrmtoolsSectionParser, HeaderError, HeaderErrorKind, HeaderValue},
};

/// Any error from the Yacc parser returns an instance of this struct.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct ASTModificationError {
    kind: YaccGrammarErrorKind,
}

impl Error for ASTModificationError {}

impl fmt::Display for ASTModificationError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.kind)
    }
}

/// Contains a `GrammarAST` structure produced from a grammar source file.
/// As well as any errors which occurred during the construction of the AST.
#[derive(Debug, Clone)]
#[cfg_attr(test, derive(PartialEq))]
pub struct ASTWithValidityInfo {
    yacc_kind: YaccKind,
    ast: GrammarAST,
    errs: Vec<YaccGrammarError>,
}

impl ASTWithValidityInfo {
    /// Parses a source file into an AST, returning an ast and any errors that were
    /// encountered during the construction of it.  The `ASTWithValidityInfo` can be
    /// then unused to construct a `YaccGrammar`, which will either produce an
    /// `Ok(YaccGrammar)` or an `Err` which includes these errors.
    ///
    /// This function ignores the `%grmtools` section entirely, assuming that the caller has
    /// already extracted the `YaccKind` if any.
    pub fn new(yacc_kind: YaccKind, s: &str) -> Self {
        let mut errs = Vec::new();
        let ast = {
            let mut yp = YaccParser::new(yacc_kind, s);
            yp.parse().map_err(|e| errs.extend(e)).ok();
            let mut ast = yp.build();
            ast.complete_and_validate().map_err(|e| errs.push(e)).ok();
            ast
        };
        ASTWithValidityInfo {
            ast,
            errs,
            yacc_kind,
        }
    }

    /// Returns a `GrammarAST` constructed as the result of parsing a source file.
    /// When errors have occurred and `is_valid` returns false, this AST is the
    /// subset of the source file which parsed correctly while not encountering
    /// any errors. As such even when an AST is not valid, it will return an AST.
    pub fn ast(&self) -> &GrammarAST {
        &self.ast
    }

    /// Returns whether any errors where encountered during the
    /// parsing and validation of the AST during it's construction.
    pub fn is_valid(&self) -> bool {
        self.errors().is_empty()
    }

    /// Returns the `YaccKind` that was used to parse the `GrammarAST`.
    pub fn yacc_kind(&self) -> YaccKind {
        self.yacc_kind
    }

    /// Returns all errors which were encountered during AST construction.
    pub fn errors(&self) -> &[YaccGrammarError] {
        self.errs.as_slice()
    }

    pub fn clone_and_change_start_rule(&self, rule: Rule) -> Result<Self, ASTModificationError> {
        if self.ast.get_rule(&rule.name.0).is_some() {
            let mut ret = self.clone();
            // The `Span`of the `start` field and the `name` field typically differ
            // in that `start` is the parameter of a `%start` declaration, while
            // `name` refers to the definition site of the rule itself.
            //
            // Lacking a better `Span` we use the definition site, for the `%start` rule here.
            ret.ast.start = Some(rule.name);
            Ok(ret)
        } else {
            Err(ASTModificationError {
                kind: YaccGrammarErrorKind::InvalidStartRule(rule.name.0),
            })
        }
    }
}

impl FromStr for ASTWithValidityInfo {
    type Err = Vec<YaccGrammarError>;
    /// Parses the `%grmtools section` expecting it to contain a `yacckind` entry.
    fn from_str(src: &str) -> Result<Self, Vec<YaccGrammarError>> {
        let mut errs = Vec::new();
        let (header, _) = GrmtoolsSectionParser::new(src, true)
            .parse()
            .map_err(|mut errs| errs.drain(..).map(|e| e.into()).collect::<Vec<_>>())?;
        if let Some(HeaderValue(_, yk_val)) = header.get("yacckind") {
            let yacc_kind = YaccKind::try_from(yk_val).map_err(|e| vec![e.into()])?;
            let ast = {
                // We don't want to strip off the header so that span's will be correct.
                let mut yp = YaccParser::new(yacc_kind, src);
                yp.parse().map_err(|e| errs.extend(e)).ok();
                let mut ast = yp.build();
                ast.complete_and_validate().map_err(|e| errs.push(e)).ok();
                ast
            };
            Ok(ASTWithValidityInfo {
                ast,
                errs,
                yacc_kind,
            })
        } else {
            Err(vec![
                HeaderError {
                    kind: HeaderErrorKind::InvalidEntry("yacckind"),
                    locations: vec![Span::new(0, 0)],
                }
                .into(),
            ])
        }
    }
}

/// An AST representing a grammar. This is built up gradually: when it is finished, the
/// `complete_and_validate` must be called exactly once in order to finish the set-up. At that
/// point, any further mutations made to the struct lead to undefined behaviour.
#[derive(Debug, Clone)]
#[cfg_attr(test, derive(PartialEq))]
#[non_exhaustive]
pub struct GrammarAST {
    pub start: Option<(String, Span)>,
    // map from a rule name to indexes into `prods`
    pub rules: IndexMap<String, Rule>,
    pub prods: Vec<Production>,
    // A set of indexes into `tokens` for all tokens in `%token` directives.
    // e.g. given a `%token a` and a token "b" not specified in any `%token` directive
    // we have `self.tokens.get_index_of("a") ∈ self.token_directives`. However for
    // token "b" we have `self.tokens.get_index_of("b") ∉ self.token_directives`.
    pub token_directives: HashSet<usize>,
    pub tokens: IndexSet<String>,
    pub spans: Vec<Span>,
    pub precs: HashMap<String, (Precedence, Span)>,
    pub avoid_insert: Option<HashMap<String, Span>>,
    pub implicit_tokens: Option<HashMap<String, Span>>,
    // Error pretty-printers,
    // The first span of the value is the span of the key,
    // The second span in the value, is the span of the values string.
    pub epp: HashMap<String, (Span, (String, Span))>,
    pub expect: Option<(usize, Span)>,
    pub expectrr: Option<(usize, Span)>,
    pub parse_param: Option<(String, String)>,
    pub programs: Option<String>,
    // The set of symbol names that, if unused in a
    // grammar, will not cause a warning or error.
    pub expect_unused: Vec<Symbol>,
}

#[derive(Debug, Clone)]
#[cfg_attr(test, derive(Eq, PartialEq))]
pub struct Rule {
    pub name: (String, Span),
    pub pidxs: Vec<usize>, // index into GrammarAST.prod
    pub actiont: Option<String>,
}

#[derive(Debug, Clone)]
#[cfg_attr(test, derive(Eq, PartialEq))]
pub struct Production {
    pub symbols: Vec<Symbol>,
    pub precedence: Option<String>,
    pub action: Option<String>,
    pub prod_span: Span,
}

#[derive(Clone, Debug)]
#[cfg_attr(test, derive(Eq, PartialEq))]
pub enum Symbol {
    Rule(String, Span),
    Token(String, Span),
}

/// Specifies an index into a `GrammarAst.tokens` or a `GrammarAST.rules`.
/// Unlike `cfgrammar::Symbol` it is not parameterized by a `StorageT`.
#[derive(Eq, PartialEq, Debug, Copy, Clone)]
pub(crate) enum SymbolIdx {
    Rule(usize),
    Token(usize),
}

impl SymbolIdx {
    pub(crate) fn symbol(self, ast: &GrammarAST) -> Symbol {
        match self {
            SymbolIdx::Rule(idx) => {
                let (rule_name, rule_span) = &ast.rules[idx].name;
                Symbol::Rule(rule_name.clone(), *rule_span)
            }
            SymbolIdx::Token(idx) => {
                let tok = &ast.tokens[idx];
                Symbol::Token(tok.clone(), ast.spans[idx])
            }
        }
    }
}
impl fmt::Display for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Symbol::Rule(ref s, _) => write!(f, "{}", s),
            Symbol::Token(ref s, _) => write!(f, "{}", s),
        }
    }
}

impl GrammarAST {
    pub fn new() -> GrammarAST {
        GrammarAST {
            start: None,
            rules: IndexMap::new(), // Using an IndexMap means that we retain the order
            // of rules as they're found in the input file.
            prods: Vec::new(),
            spans: Vec::new(),
            tokens: IndexSet::new(),
            token_directives: HashSet::new(),
            precs: HashMap::new(),
            avoid_insert: None,
            implicit_tokens: None,
            epp: HashMap::new(),
            expect: None,
            expectrr: None,
            parse_param: None,
            programs: None,
            expect_unused: Vec::new(),
        }
    }

    pub fn add_rule(&mut self, (name, name_span): (String, Span), actiont: Option<String>) {
        self.rules.insert(
            name.clone(),
            Rule {
                name: (name, name_span),
                pidxs: Vec::new(),
                actiont,
            },
        );
    }

    pub fn add_prod(
        &mut self,
        rule_name: String,
        symbols: Vec<Symbol>,
        precedence: Option<String>,
        action: Option<String>,
        prod_span: Span,
    ) {
        self.rules[&rule_name].pidxs.push(self.prods.len());
        self.prods.push(Production {
            symbols,
            precedence,
            action,
            prod_span,
        });
    }

    #[deprecated(since = "0.10.2", note = "Please use set_programs instead")]
    pub fn add_programs(&mut self, s: String) {
        self.set_programs(s);
    }

    pub fn set_programs(&mut self, s: String) {
        self.programs = Some(s)
    }

    pub fn get_rule(&self, key: &str) -> Option<&Rule> {
        self.rules.get(key)
    }

    pub fn has_token(&self, s: &str) -> bool {
        self.tokens.contains(s)
    }

    /// After the AST has been populated, perform any final operations, and validate the grammar
    /// checking that:
    ///   1) The start rule references a rule in the grammar
    ///   2) Every rule reference references a rule in the grammar
    ///   3) Every token reference references a declared token
    ///   4) If a production has a precedence token, then it references a declared token
    ///   5) Every token declared with %epp matches a known token
    ///
    /// If the validation succeeds, None is returned.
    pub(crate) fn complete_and_validate(&mut self) -> Result<(), YaccGrammarError> {
        match self.start {
            None => {
                return Err(YaccGrammarError {
                    kind: YaccGrammarErrorKind::NoStartRule,
                    spans: vec![Span::new(0, 0)],
                });
            }
            Some((ref s, span)) => {
                if !self.rules.contains_key(s) {
                    return Err(YaccGrammarError {
                        kind: YaccGrammarErrorKind::InvalidStartRule(s.clone()),
                        spans: vec![span],
                    });
                }
            }
        }
        for rule in self.rules.values() {
            for &pidx in &rule.pidxs {
                let prod = &self.prods[pidx];
                if let Some(ref n) = prod.precedence {
                    if !self.tokens.contains(n) {
                        return Err(YaccGrammarError {
                            kind: YaccGrammarErrorKind::UnknownToken(n.clone()),
                            spans: vec![Span::new(0, 0)],
                        });
                    }
                    if !self.precs.contains_key(n) {
                        return Err(YaccGrammarError {
                            kind: YaccGrammarErrorKind::NoPrecForToken(n.clone()),
                            spans: vec![Span::new(0, 0)],
                        });
                    }
                }
                for sym in &prod.symbols {
                    match *sym {
                        Symbol::Rule(ref name, span) => {
                            if !self.rules.contains_key(name) {
                                return Err(YaccGrammarError {
                                    kind: YaccGrammarErrorKind::UnknownRuleRef(name.clone()),
                                    spans: vec![span],
                                });
                            }
                        }
                        Symbol::Token(ref name, span) => {
                            if !self.tokens.contains(name) {
                                return Err(YaccGrammarError {
                                    kind: YaccGrammarErrorKind::UnknownToken(name.clone()),
                                    spans: vec![span],
                                });
                            }
                        }
                    }
                }
            }
        }

        for (k, (sp, _)) in self.epp.iter() {
            if self.tokens.contains(k) {
                continue;
            }
            if let Some(ref it) = self.implicit_tokens {
                if it.contains_key(k) {
                    continue;
                }
            }
            return Err(YaccGrammarError {
                kind: YaccGrammarErrorKind::UnknownEPP(k.clone()),
                spans: vec![*sp],
            });
        }

        for sym in &self.expect_unused {
            match sym {
                Symbol::Rule(sym_name, sym_span) => {
                    if self.get_rule(sym_name).is_none() {
                        return Err(YaccGrammarError {
                            kind: YaccGrammarErrorKind::UnknownRuleRef(sym_name.clone()),
                            spans: vec![*sym_span],
                        });
                    }
                }
                Symbol::Token(sym_name, sym_span) => {
                    if !self.has_token(sym_name) {
                        return Err(YaccGrammarError {
                            kind: YaccGrammarErrorKind::UnknownToken(sym_name.clone()),
                            spans: vec![*sym_span],
                        });
                    }
                }
            }
        }
        Ok(())
    }

    pub fn warnings(&self) -> Vec<YaccGrammarWarning> {
        self.unused_symbols()
            .map(|symidx| {
                let (kind, span) = match symidx.symbol(self) {
                    Symbol::Rule(_, span) => (YaccGrammarWarningKind::UnusedRule, span),
                    Symbol::Token(_, span) => (YaccGrammarWarningKind::UnusedToken, span),
                };
                YaccGrammarWarning {
                    kind,
                    spans: vec![span],
                }
            })
            .collect()
    }

    /// Return the indices of unexpectedly unused rules (relative to ast.rules)
    /// and tokens (relative to ast.tokens) as `SymbolIdx`s.
    pub(crate) fn unused_symbols(&self) -> impl Iterator<Item = SymbolIdx> + '_ {
        let start_rule_name = self.start.as_ref().map(|(name, _)| name.clone());
        let start_rule = self
            .rules
            .iter()
            .find(|(rule_name, _)| start_rule_name.as_ref() == Some(rule_name));
        let mut seen_rules = HashSet::new();
        let mut seen_tokens = HashSet::new();
        let mut expected_unused_tokens = HashSet::new();
        let mut expected_unused_rules = HashSet::new();
        for sym in &self.expect_unused {
            match sym {
                Symbol::Rule(sym_name, _) => {
                    expected_unused_rules.insert(sym_name);
                }
                Symbol::Token(sym_name, _) => {
                    expected_unused_tokens.insert(sym_name);
                }
            }
        }
        if let Some(implicit_tokens) = self.implicit_tokens.as_ref() {
            expected_unused_tokens.extend(implicit_tokens.keys())
        }
        if let Some((start_name, start_rule)) = start_rule {
            let mut todo = Vec::new();
            todo.extend(start_rule.pidxs.iter().copied());
            seen_rules.insert(start_name);

            while let Some(pidx) = todo.pop() {
                let prod = &self.prods[pidx];
                for sym in &prod.symbols {
                    match sym {
                        Symbol::Rule(name, _) => {
                            if seen_rules.insert(name) {
                                if let Some(rule) = self.rules.get(name) {
                                    todo.extend(&rule.pidxs);
                                }
                            }
                        }
                        Symbol::Token(name, _) => {
                            seen_tokens.insert(name);
                        }
                    };
                }
            }
        }
        self.rules
            .iter()
            .enumerate()
            .filter_map(move |(rule_id, (rule_name, _))| {
                if expected_unused_rules.contains(rule_name) || seen_rules.contains(rule_name) {
                    None
                } else {
                    Some(SymbolIdx::Rule(rule_id))
                }
            })
            .chain(
                self.tokens
                    .iter()
                    .enumerate()
                    .filter_map(move |(tok_idx, tok)| {
                        if expected_unused_tokens.contains(tok) || seen_tokens.contains(tok) {
                            None
                        } else {
                            Some(SymbolIdx::Token(tok_idx))
                        }
                    }),
            )
    }
}

#[cfg(test)]
mod test {
    use super::{
        super::{AssocKind, Precedence},
        GrammarAST, Span, Symbol, YaccGrammarError, YaccGrammarErrorKind,
    };

    fn rule(n: &str) -> Symbol {
        Symbol::Rule(n.to_string(), Span::new(0, 0))
    }

    fn token(n: &str) -> Symbol {
        Symbol::Token(n.to_string(), Span::new(0, 0))
    }

    #[test]
    fn test_empty_grammar() {
        let mut grm = GrammarAST::new();
        match grm.complete_and_validate() {
            Err(YaccGrammarError {
                kind: YaccGrammarErrorKind::NoStartRule,
                ..
            }) => (),
            _ => panic!("Validation error"),
        }
    }

    #[test]
    fn test_invalid_start_rule() {
        let mut grm = GrammarAST::new();
        let empty_span = Span::new(0, 0);
        grm.start = Some(("A".to_string(), empty_span));
        grm.add_rule(("B".to_string(), empty_span), None);
        grm.add_prod("B".to_string(), vec![], None, None, empty_span);
        match grm.complete_and_validate() {
            Err(YaccGrammarError {
                kind: YaccGrammarErrorKind::InvalidStartRule(_),
                ..
            }) => (),
            _ => panic!("Validation error"),
        }
    }

    #[test]
    fn test_valid_start_rule() {
        let mut grm = GrammarAST::new();
        let empty_span = Span::new(0, 0);
        grm.start = Some(("A".to_string(), empty_span));
        grm.add_rule(("A".to_string(), empty_span), None);
        grm.add_prod("A".to_string(), vec![], None, None, empty_span);
        assert!(grm.complete_and_validate().is_ok());
    }

    #[test]
    fn test_valid_rule_ref() {
        let mut grm = GrammarAST::new();
        let empty_span = Span::new(0, 0);
        grm.start = Some(("A".to_string(), empty_span));
        grm.add_rule(("A".to_string(), empty_span), None);
        grm.add_rule(("B".to_string(), empty_span), None);
        grm.add_prod("A".to_string(), vec![rule("B")], None, None, empty_span);
        grm.add_prod("B".to_string(), vec![], None, None, empty_span);
        assert!(grm.complete_and_validate().is_ok());
    }

    #[test]
    fn test_invalid_rule_ref() {
        let mut grm = GrammarAST::new();
        let empty_span = Span::new(0, 0);
        grm.start = Some(("A".to_string(), empty_span));
        grm.add_rule(("A".to_string(), empty_span), None);
        grm.add_prod("A".to_string(), vec![rule("B")], None, None, empty_span);
        match grm.complete_and_validate() {
            Err(YaccGrammarError {
                kind: YaccGrammarErrorKind::UnknownRuleRef(_),
                ..
            }) => (),
            _ => panic!("Validation error"),
        }
    }

    #[test]
    fn test_valid_token_ref() {
        let mut grm = GrammarAST::new();
        let empty_span = Span::new(0, 0);
        grm.tokens.insert("b".to_string());
        grm.start = Some(("A".to_string(), empty_span));
        grm.add_rule(("A".to_string(), empty_span), None);
        grm.add_prod("A".to_string(), vec![token("b")], None, None, empty_span);
        assert!(grm.complete_and_validate().is_ok());
    }

    #[test]
    fn test_redefine_rules_as_tokens() {
        // for now we won't support the YACC feature that allows
        // to redefine rules as tokens by adding them to '%token'
        let mut grm = GrammarAST::new();
        let empty_span = Span::new(0, 0);
        grm.tokens.insert("b".to_string());
        grm.start = Some(("A".to_string(), empty_span));
        grm.add_rule(("A".to_string(), empty_span), None);
        grm.add_prod("A".to_string(), vec![rule("b")], None, None, empty_span);
        assert!(grm.complete_and_validate().is_err());
    }

    #[test]
    fn test_invalid_token_ref() {
        let mut grm = GrammarAST::new();
        let empty_span = Span::new(0, 0);
        grm.start = Some(("A".to_string(), empty_span));
        grm.add_rule(("A".to_string(), empty_span), None);
        grm.add_prod("A".to_string(), vec![token("b")], None, None, empty_span);
        match grm.complete_and_validate() {
            Err(YaccGrammarError {
                kind: YaccGrammarErrorKind::UnknownToken(_),
                ..
            }) => (),
            _ => panic!("Validation error"),
        }
    }

    #[test]
    fn test_invalid_rule_forgotten_token() {
        let mut grm = GrammarAST::new();
        let empty_span = Span::new(0, 0);
        grm.start = Some(("A".to_string(), empty_span));
        grm.add_rule(("A".to_string(), empty_span), None);
        grm.add_prod(
            "A".to_string(),
            vec![rule("b"), token("b")],
            None,
            None,
            Span::new(0, 2),
        );
        match grm.complete_and_validate() {
            Err(YaccGrammarError {
                kind: YaccGrammarErrorKind::UnknownRuleRef(_),
                ..
            }) => (),
            _ => panic!("Validation error"),
        }
    }

    #[test]
    fn test_invalid_epp() {
        let mut grm = GrammarAST::new();
        let empty_span = Span::new(2, 3);
        grm.start = Some(("A".to_string(), empty_span));
        grm.add_rule(("A".to_string(), empty_span), None);
        grm.add_prod("A".to_string(), vec![], None, None, empty_span);
        grm.epp
            .insert("k".to_owned(), (empty_span, ("v".to_owned(), empty_span)));
        match grm.complete_and_validate() {
            Err(YaccGrammarError {
                kind: YaccGrammarErrorKind::UnknownEPP(_),
                spans,
            }) if spans.len() == 1 && spans[0] == Span::new(2, 3) => (),
            _ => panic!("Validation error"),
        }
    }

    #[test]
    fn test_precedence_override() {
        let mut grm = GrammarAST::new();
        let empty_span = Span::new(0, 0);
        grm.precs.insert(
            "b".to_string(),
            (
                Precedence {
                    level: 1,
                    kind: AssocKind::Left,
                },
                Span::new(0, 0),
            ),
        );
        grm.start = Some(("A".to_string(), empty_span));
        grm.tokens.insert("b".to_string());
        grm.add_rule(("A".to_string(), empty_span), None);
        grm.add_prod(
            "A".to_string(),
            vec![token("b")],
            Some("b".to_string()),
            None,
            empty_span,
        );
        assert!(grm.complete_and_validate().is_ok());
    }

    #[test]
    fn test_invalid_precedence_override() {
        let mut grm = GrammarAST::new();
        let empty_span = Span::new(0, 0);
        grm.start = Some(("A".to_string(), empty_span));
        grm.add_rule(("A".to_string(), empty_span), None);
        grm.add_prod(
            "A".to_string(),
            vec![token("b")],
            Some("b".to_string()),
            None,
            empty_span,
        );
        match grm.complete_and_validate() {
            Err(YaccGrammarError {
                kind: YaccGrammarErrorKind::UnknownToken(_),
                ..
            }) => (),
            _ => panic!("Validation error"),
        }
        grm.tokens.insert("b".to_string());
        match grm.complete_and_validate() {
            Err(YaccGrammarError {
                kind: YaccGrammarErrorKind::NoPrecForToken(_),
                ..
            }) => (),
            _ => panic!("Validation error"),
        }
    }

    #[test]
    fn test_ast_unused_symbols() {
        let mut grm = GrammarAST::new();
        let empty_span = Span::new(0, 0);
        grm.start = Some(("A".to_string(), empty_span));
        grm.add_rule(("A".to_string(), empty_span), None);
        grm.add_prod("A".to_string(), vec![], None, None, empty_span);
        grm.tokens.insert("b".to_string());
        grm.spans.push(Span::new(4, 5));
        grm.add_rule(("B".to_string(), Span::new(1, 2)), None);
        grm.add_prod("B".to_string(), vec![token("b")], None, None, empty_span);

        assert_eq!(
            grm.unused_symbols()
                .map(|sym_idx| sym_idx.symbol(&grm))
                .collect::<Vec<Symbol>>()
                .as_slice(),
            &[
                Symbol::Rule("B".to_string(), Span::new(1, 2)),
                Symbol::Token("b".to_string(), Span::new(4, 5))
            ]
        )
    }

    #[test]
    fn token_rule_confusion_issue_557() {
        use super::*;
        use crate::yacc::*;
        let ast_validity = ASTWithValidityInfo::new(
            YaccKind::Original(YaccOriginalActionKind::GenericParseTree),
            r#"
            %start start
            %%
            start: "a" a;
            a: "c";"#,
        );
        assert!(
            ast_validity.ast().prods[0]
                .symbols
                .contains(&Symbol::Rule("a".to_string(), Span::new(64, 65)))
        );
        let ast_validity = ASTWithValidityInfo::new(
            YaccKind::Original(YaccOriginalActionKind::GenericParseTree),
            r#"
            %start start
            %%
            start: "a" x;
            x: "c";"#,
        );
        assert!(
            ast_validity.ast().prods[0]
                .symbols
                .contains(&Symbol::Rule("x".to_string(), Span::new(64, 65)))
        );
        let ast_validity = ASTWithValidityInfo::new(
            YaccKind::Original(YaccOriginalActionKind::GenericParseTree),
            r#"
        %start start
        %token a
        %%
        start: "a" a;
        "#,
        );
        assert_eq!(
            ast_validity.ast().prods[0].symbols,
            [
                Symbol::Token("a".to_string(), Span::new(66, 67)),
                Symbol::Token("a".to_string(), Span::new(69, 70))
            ]
        );
    }

    #[test]
    fn test_token_directives() {
        use super::*;
        use crate::yacc::*;

        // Testing that `%token a` after `%left "a"` still ends up in
        let ast_validity = ASTWithValidityInfo::new(
            YaccKind::Original(YaccOriginalActionKind::GenericParseTree),
            r#"
                %left "a"
                %token a
                %start start
                %%
                start: "a" a "b";
                "#,
        );
        assert!(
            ast_validity
                .ast()
                .token_directives
                .contains(&ast_validity.ast().tokens.get_index_of("a").unwrap())
        );
        assert!(
            !ast_validity
                .ast()
                .token_directives
                .contains(&ast_validity.ast().tokens.get_index_of("b").unwrap())
        );
    }

    #[test]
    fn clone_ast_changing_start_rule() {
        use super::*;
        use crate::yacc::*;
        let y_src = r#"
        %start AStart
        %token A B C
        %%
        AStart: A ':' BStart ';';
        BStart: B ',' C | C ',' B;
        "#;

        let astart_ast_validity =
            ASTWithValidityInfo::new(YaccKind::Original(YaccOriginalActionKind::NoAction), &y_src);
        let bstart_rule = astart_ast_validity.ast().get_rule("BStart").unwrap();
        let bstart_ast_validity = astart_ast_validity
            .clone_and_change_start_rule(bstart_rule.clone())
            .unwrap();
        assert!(astart_ast_validity.is_valid());
        assert!(bstart_ast_validity.is_valid());
        assert_eq!(
            bstart_ast_validity.ast().start.as_ref(),
            Some(&bstart_rule.name)
        );
    }
}
