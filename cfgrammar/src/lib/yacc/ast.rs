use std::{
    collections::{HashMap, HashSet},
    fmt,
};

use indexmap::{IndexMap, IndexSet};

use super::{
    parser::YaccGrammarConstructionFailure, parser::YaccParser, Precedence, YaccGrammarError,
    YaccGrammarErrorKind, YaccGrammarWarning, YaccGrammarWarningKind, YaccKind,
};
use crate::Span;
use std::path;
use std::sync::mpsc;
/// Contains a `GrammarAST` structure produced from a grammar source file.
/// As well as any errors which occurred during the construction of the AST.
pub struct ASTWithValidityInfo {
    pub(crate) ast: GrammarAST,
    pub(crate) error_receiver: Option<mpsc::Receiver<YaccGrammarError>>,
    pub(crate) error_sender: ErrorSender,
}

#[allow(dead_code)]
pub struct AstBuilder<'a> {
    kind: YaccKind,
    grammar_src: Option<&'a str>,
    grammar_path: Option<path::PathBuf>,
    error_receiver: Option<mpsc::Receiver<YaccGrammarError>>,
    error_sender: ErrorSender,
}

pub struct ErrorSender {
    error_occurred: bool,
    sender: Option<mpsc::Sender<YaccGrammarError>>,
}

#[allow(dead_code)]
impl ErrorSender {
    pub(crate) fn new(sender: mpsc::Sender<YaccGrammarError>) -> Self {
        Self {
            error_occurred: false,
            sender: Some(sender),
        }
    }
    pub(crate) fn close(&mut self) {
        drop(self.sender.take())
    }

    pub(crate) fn send(
        &mut self,
        e: YaccGrammarError,
    ) -> Result<(), mpsc::SendError<YaccGrammarError>> {
        self.error_occurred = true;
        if let Some(sender) = &self.sender {
            sender.send(e)
        } else {
            Err(mpsc::SendError(e))
        }
    }
    pub(crate) fn error_occurred(&self) -> bool {
        self.error_occurred
    }
}

#[allow(dead_code)]
impl<'a> AstBuilder<'a> {
    fn path(mut self, path: &path::Path) -> Self {
        self.grammar_path = Some(path.to_owned());
        self
    }
    fn yacc_kind(mut self, kind: YaccKind) -> Self {
        self.kind = kind;
        self
    }

    fn error_receiver(&mut self) -> mpsc::Receiver<YaccGrammarError> {
        self.error_receiver.take().unwrap()
    }

    fn build(self) -> ASTWithValidityInfo {
        ASTWithValidityInfo::new_with_error_channel(
            self.kind,
            self.grammar_src.unwrap(),
            self.error_sender,
            self.error_receiver,
        )
    }
}

impl<'a> ASTWithValidityInfo {
    pub fn builder() -> AstBuilder<'a> {
        let (error_sender, error_receiver) = std::sync::mpsc::channel();
        AstBuilder {
            kind: YaccKind::Grmtools,
            grammar_src: None,
            grammar_path: None,
            error_receiver: Some(error_receiver),
            error_sender: ErrorSender::new(error_sender),
        }
    }

    pub fn new_with_error_channel(
        yacc_kind: YaccKind,
        s: &str,
        mut error_sender: ErrorSender,
        error_receiver: Option<mpsc::Receiver<YaccGrammarError>>,
    ) -> Self {
        let ast = match yacc_kind {
            YaccKind::Original(_) | YaccKind::Grmtools | YaccKind::Eco => {
                let mut yp = YaccParser::new(yacc_kind, s.to_string());
                yp.parse_with_error_channel(&mut error_sender).unwrap();
                let mut ast = yp.ast();
                ast.complete_and_validate_with_error_channel(&mut error_sender)
                    .ok();
                ast
            }
        };
        error_sender.close();
        ASTWithValidityInfo {
            ast,
            error_receiver,
            error_sender,
        }
    }

    #[cfg(test)]
    pub(crate) fn validate_ast(mut ast: GrammarAST) -> Self {
        let (error_sender, error_receiver) = mpsc::channel();
        let mut error_sender = ErrorSender::new(error_sender);
        ast.complete_and_validate_with_error_channel(&mut error_sender)
            .ok();
        error_sender.close();
        ASTWithValidityInfo {
            ast,
            error_receiver: Some(error_receiver),
            error_sender,
        }
    }

    /// Parses a source file into an AST, returning an ast and any errors that were
    /// encountered during the construction of it.  The `ASTWithValidityInfo` can be
    /// then unused to construct a `YaccGrammar`, which will either produce an
    /// `Ok(YaccGrammar)` or an `Err` which includes these errors.
    pub fn new(yacc_kind: YaccKind, s: &str) -> Self {
        let (error_sender, error_receiver) = mpsc::channel();
        let mut error_sender = ErrorSender::new(error_sender);
        let ast = match yacc_kind {
            YaccKind::Original(_) | YaccKind::Grmtools | YaccKind::Eco => {
                let mut yp = YaccParser::new(yacc_kind, s.to_string());
                let _ = yp.parse_with_error_channel(&mut error_sender).ok();
                let mut ast = yp.ast();
                ast.complete_and_validate_with_error_channel(&mut error_sender)
                    .ok();
                error_sender.close();
                ast
            }
        };
        ASTWithValidityInfo {
            ast,
            error_receiver: Some(error_receiver),
            error_sender,
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
        !self.error_sender.error_occurred()
    }

    /// Returns all errors which were encountered during AST construction.
    pub fn errors(&self) -> Vec<YaccGrammarError> {
        let errs = self
            .error_receiver
            .as_ref()
            .map_or(vec![], |errs| errs.iter().collect::<Vec<_>>());
        errs
    }
}

/// An AST representing a grammar. This is built up gradually: when it is finished, the
/// `complete_and_validate` must be called exactly once in order to finish the set-up. At that
/// point, any further mutations made to the struct lead to undefined behaviour.
#[derive(Debug)]
pub struct GrammarAST {
    pub start: Option<(String, Span)>,
    // map from a rule name to indexes into prods
    pub rules: IndexMap<String, Rule>,
    pub prods: Vec<Production>,
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

#[derive(Debug)]
pub struct Rule {
    pub name: (String, Span),
    pub pidxs: Vec<usize>, // index into GrammarAST.prod
    pub actiont: Option<String>,
}

#[derive(Debug)]
#[cfg_attr(test, derive(Eq, PartialEq))]
pub struct Production {
    pub symbols: Vec<Symbol>,
    pub precedence: Option<String>,
    pub action: Option<String>,
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
    ) {
        self.rules[&rule_name].pidxs.push(self.prods.len());
        self.prods.push(Production {
            symbols,
            precedence,
            action,
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
    /// If the validation succeeds, None is returned.
    pub(crate) fn complete_and_validate_with_error_channel(
        &mut self,
        errs: &mut ErrorSender,
    ) -> Result<(), YaccGrammarConstructionFailure> {
        match self.start {
            None => {
                errs.send(YaccGrammarError {
                    kind: YaccGrammarErrorKind::NoStartRule,
                    spans: vec![Span::new(0, 0)],
                })?;
                return Err(YaccGrammarConstructionFailure::ConstructionFailure);
            }
            Some((ref s, span)) => {
                if !self.rules.contains_key(s) {
                    errs.send(YaccGrammarError {
                        kind: YaccGrammarErrorKind::InvalidStartRule(s.clone()),
                        spans: vec![span],
                    })?;
                    return Err(YaccGrammarConstructionFailure::ConstructionFailure);
                }
            }
        }
        for rule in self.rules.values() {
            for &pidx in &rule.pidxs {
                let prod = &self.prods[pidx];
                if let Some(ref n) = prod.precedence {
                    if !self.tokens.contains(n) {
                        errs.send(YaccGrammarError {
                            kind: YaccGrammarErrorKind::UnknownToken(n.clone()),
                            spans: vec![Span::new(0, 0)],
                        })?;
                        return Err(YaccGrammarConstructionFailure::ConstructionFailure);
                    }
                    if !self.precs.contains_key(n) {
                        errs.send(YaccGrammarError {
                            kind: YaccGrammarErrorKind::NoPrecForToken(n.clone()),
                            spans: vec![Span::new(0, 0)],
                        })?;
                        return Err(YaccGrammarConstructionFailure::ConstructionFailure);
                    }
                }
                for sym in &prod.symbols {
                    match *sym {
                        Symbol::Rule(ref name, span) => {
                            if !self.rules.contains_key(name) {
                                errs.send(YaccGrammarError {
                                    kind: YaccGrammarErrorKind::UnknownRuleRef(name.clone()),
                                    spans: vec![span],
                                })?;
                                return Err(YaccGrammarConstructionFailure::ConstructionFailure);
                            }
                        }
                        Symbol::Token(ref name, span) => {
                            if !self.tokens.contains(name) {
                                errs.send(YaccGrammarError {
                                    kind: YaccGrammarErrorKind::UnknownToken(name.clone()),
                                    spans: vec![span],
                                })?;
                                return Err(YaccGrammarConstructionFailure::ConstructionFailure);
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
            errs.send(YaccGrammarError {
                kind: YaccGrammarErrorKind::UnknownEPP(k.clone()),
                spans: vec![*sp],
            })?;
            return Err(YaccGrammarConstructionFailure::ConstructionFailure);
        }

        for sym in &self.expect_unused {
            match sym {
                Symbol::Rule(sym_name, sym_span) => {
                    if self.get_rule(sym_name).is_none() {
                        errs.send(YaccGrammarError {
                            kind: YaccGrammarErrorKind::UnknownRuleRef(sym_name.clone()),
                            spans: vec![*sym_span],
                        })?;
                        return Err(YaccGrammarConstructionFailure::ConstructionFailure);
                    }
                }
                Symbol::Token(sym_name, sym_span) => {
                    if !self.has_token(sym_name) {
                        errs.send(YaccGrammarError {
                            kind: YaccGrammarErrorKind::UnknownToken(sym_name.clone()),
                            spans: vec![*sym_span],
                        })?;
                        return Err(YaccGrammarConstructionFailure::ConstructionFailure);
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
        ASTWithValidityInfo, GrammarAST, Span, Symbol, YaccGrammarError, YaccGrammarErrorKind,
    };

    fn rule(n: &str) -> Symbol {
        Symbol::Rule(n.to_string(), Span::new(0, 0))
    }

    fn token(n: &str) -> Symbol {
        Symbol::Token(n.to_string(), Span::new(0, 0))
    }

    #[test]
    fn test_empty_grammar() {
        let grm = GrammarAST::new();
        match ASTWithValidityInfo::validate_ast(grm).errors().as_slice() {
            [YaccGrammarError {
                kind: YaccGrammarErrorKind::NoStartRule,
                ..
            }] => (),
            _ => panic!("Validation error"),
        }
    }

    #[test]
    fn test_invalid_start_rule() {
        let mut grm = GrammarAST::new();
        let empty_span = Span::new(0, 0);
        grm.start = Some(("A".to_string(), empty_span));
        grm.add_rule(("B".to_string(), empty_span), None);
        grm.add_prod("B".to_string(), vec![], None, None);

        match ASTWithValidityInfo::validate_ast(grm).errors().as_slice() {
            [YaccGrammarError {
                kind: YaccGrammarErrorKind::InvalidStartRule(_),
                ..
            }] => (),
            _ => panic!("Validation error"),
        }
    }

    #[test]
    fn test_valid_start_rule() {
        let mut grm = GrammarAST::new();
        let empty_span = Span::new(0, 0);
        grm.start = Some(("A".to_string(), empty_span));
        grm.add_rule(("A".to_string(), empty_span), None);
        grm.add_prod("A".to_string(), vec![], None, None);
        assert!(ASTWithValidityInfo::validate_ast(grm).is_valid());
    }

    #[test]
    fn test_valid_rule_ref() {
        let mut grm = GrammarAST::new();
        let empty_span = Span::new(0, 0);
        grm.start = Some(("A".to_string(), empty_span));
        grm.add_rule(("A".to_string(), empty_span), None);
        grm.add_rule(("B".to_string(), empty_span), None);
        grm.add_prod("A".to_string(), vec![rule("B")], None, None);
        grm.add_prod("B".to_string(), vec![], None, None);
        assert!(ASTWithValidityInfo::validate_ast(grm).is_valid());
    }

    #[test]
    fn test_invalid_rule_ref() {
        let mut grm = GrammarAST::new();
        let empty_span = Span::new(0, 0);
        grm.start = Some(("A".to_string(), empty_span));
        grm.add_rule(("A".to_string(), empty_span), None);
        grm.add_prod("A".to_string(), vec![rule("B")], None, None);
        match ASTWithValidityInfo::validate_ast(grm).errors().as_slice() {
            [YaccGrammarError {
                kind: YaccGrammarErrorKind::UnknownRuleRef(_),
                ..
            }] => (),
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
        grm.add_prod("A".to_string(), vec![token("b")], None, None);
        assert!(ASTWithValidityInfo::validate_ast(grm).is_valid());
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
        grm.add_prod("A".to_string(), vec![rule("b")], None, None);
        assert!(!ASTWithValidityInfo::validate_ast(grm).is_valid());
    }

    #[test]
    fn test_invalid_token_ref() {
        let mut grm = GrammarAST::new();
        let empty_span = Span::new(0, 0);
        grm.start = Some(("A".to_string(), empty_span));
        grm.add_rule(("A".to_string(), empty_span), None);
        grm.add_prod("A".to_string(), vec![token("b")], None, None);
        match ASTWithValidityInfo::validate_ast(grm).errors().as_slice() {
            [YaccGrammarError {
                kind: YaccGrammarErrorKind::UnknownToken(_),
                ..
            }] => (),
            _ => panic!("Validation error"),
        }
    }

    #[test]
    fn test_invalid_rule_forgotten_token() {
        let mut grm = GrammarAST::new();
        let empty_span = Span::new(0, 0);
        grm.start = Some(("A".to_string(), empty_span));
        grm.add_rule(("A".to_string(), empty_span), None);
        grm.add_prod("A".to_string(), vec![rule("b"), token("b")], None, None);
        match ASTWithValidityInfo::validate_ast(grm).errors().as_slice() {
            [YaccGrammarError {
                kind: YaccGrammarErrorKind::UnknownRuleRef(_),
                ..
            }] => (),
            _ => panic!("Validation error"),
        }
    }

    #[test]
    fn test_invalid_epp() {
        let mut grm = GrammarAST::new();
        let empty_span = Span::new(2, 3);
        grm.start = Some(("A".to_string(), empty_span));
        grm.add_rule(("A".to_string(), empty_span), None);
        grm.add_prod("A".to_string(), vec![], None, None);
        grm.epp
            .insert("k".to_owned(), (empty_span, ("v".to_owned(), empty_span)));
        match ASTWithValidityInfo::validate_ast(grm).errors().as_slice() {
            [YaccGrammarError {
                kind: YaccGrammarErrorKind::UnknownEPP(_),
                spans,
            }] if spans.len() == 1 && spans[0] == Span::new(2, 3) => (),
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
        );
        assert!(ASTWithValidityInfo::validate_ast(grm).is_valid());
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
        );
        match ASTWithValidityInfo::validate_ast(grm).errors().as_slice() {
            [YaccGrammarError {
                kind: YaccGrammarErrorKind::UnknownToken(_),
                ..
            }] => (),
            _ => panic!("Validation error"),
        }
        let mut grm = GrammarAST::new();
        grm.start = Some(("A".to_string(), empty_span));
        grm.add_rule(("A".to_string(), empty_span), None);
        grm.add_prod(
            "A".to_string(),
            vec![token("b")],
            Some("b".to_string()),
            None,
        );
        grm.tokens.insert("b".to_string());
        match ASTWithValidityInfo::validate_ast(grm).errors().as_slice() {
            [YaccGrammarError {
                kind: YaccGrammarErrorKind::NoPrecForToken(_),
                ..
            }] => (),
            _ => panic!("Validation error"),
        }
    }

    #[test]
    fn test_ast_unused_symbols() {
        let mut grm = GrammarAST::new();
        let empty_span = Span::new(0, 0);
        grm.start = Some(("A".to_string(), empty_span));
        grm.add_rule(("A".to_string(), empty_span), None);
        grm.add_prod("A".to_string(), vec![], None, None);
        grm.tokens.insert("b".to_string());
        grm.spans.push(Span::new(4, 5));
        grm.add_rule(("B".to_string(), Span::new(1, 2)), None);
        grm.add_prod("B".to_string(), vec![token("b")], None, None);

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
}
