use std::{
    collections::{HashMap, HashSet},
    fmt,
};

use indexmap::{IndexMap, IndexSet};

use super::parser::{YaccGrammarWarning, YaccGrammarWarningKind};
use super::{Precedence, YaccGrammarError, YaccGrammarErrorKind};

use crate::Span;

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
    // Unchecked `Symbol` names, with spans pointing into the `%expect-unused` declaration.
    pub expect_unused: Vec<Symbol>,
}

#[derive(Debug)]
pub struct Rule {
    pub name: (String, Span),
    pub pidxs: Vec<usize>, // index into GrammarAST.prods
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
        for k in self.epp.keys() {
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
                spans: vec![Span::new(0, 0)],
            });
        }

        for sym in &self.expect_unused {
            match sym {
                crate::yacc::ast::Symbol::Rule(sym_name, sym_span) => {
                    if self.get_rule(sym_name).is_none() {
                        return Err(YaccGrammarError {
                            kind: YaccGrammarErrorKind::UnknownRuleRef(sym_name.clone()),
                            spans: vec![*sym_span],
                        });
                    }
                }
                crate::yacc::ast::Symbol::Token(sym_name, sym_span) => {
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

    pub(crate) fn unused_symbol_warnings(&self) -> impl Iterator<Item = YaccGrammarWarning> {
        #[derive(Hash, PartialEq, Eq, Debug, Copy, Clone)]
        enum SymbolKind {
            Rule,
            Token,
        }
        let start_rule_name = self.start.as_ref().map(|(name, _)| name.clone());
        let start_rule = self
            .rules
            .iter()
            .find(|(rule_name, _)| start_rule_name.as_ref() == Some(rule_name));
        let mut used_symbols = HashSet::new();
        let mut expect_unused = self
            .expect_unused
            .iter()
            .filter_map(|sym| match &sym {
                Symbol::Rule(sym_name, _) => {
                    if self.rules.contains_key(sym_name) {
                        Some((sym_name, SymbolKind::Rule))
                    } else {
                        None
                    }
                }
                Symbol::Token(sym_name, _) => {
                    if self.tokens.contains(sym_name) {
                        Some((sym_name, SymbolKind::Token))
                    } else {
                        None
                    }
                }
            })
            .collect::<Vec<(&String, SymbolKind)>>();
        // If a rule is specified in `%expect-unused`, also add the tokens associated with it.
        // This perhaps should add rules as well, but i'm not quite certain.
        let mut extra_unused = Vec::new();
        for (unused_sym, _) in expect_unused.iter() {
            if let Some(rule) = self.rules.get(*unused_sym) {
                for pidx in &rule.pidxs {
                    for symbol in &self.prods[*pidx].symbols {
                        if let Symbol::Token(tok, _) = symbol {
                            extra_unused.push((tok, SymbolKind::Token));
                        }
                    }
                }
            }
        }
        expect_unused.extend(extra_unused);

        if let Some(implicit_tokens) = self.implicit_tokens.as_ref() {
            expect_unused.extend(
                implicit_tokens
                    .iter()
                    .map(|(key, _)| (key, SymbolKind::Token)),
            )
        }

        if let Some((start_name, start_rule)) = start_rule {
            let mut queue = Vec::new();
            let start_sym = (start_name, SymbolKind::Rule);
            queue.extend(start_rule.pidxs.iter().copied());
            used_symbols.insert(start_sym);

            while let Some(pidx) = queue.pop() {
                let prod = &self.prods[pidx];
                for sym in &prod.symbols {
                    let (sym_name, sym_kind) = match sym {
                        Symbol::Rule(name, _) => (name, SymbolKind::Rule),
                        Symbol::Token(name, _) => (name, SymbolKind::Token),
                    };

                    if used_symbols.insert((sym_name, sym_kind)) && sym_kind == SymbolKind::Rule {
                        if let Some(rule) = self.rules.get(sym_name) {
                            queue.extend(&rule.pidxs);
                        }
                    }
                }
            }
        }
        self.rules
            .iter()
            .filter_map(|(rule_name, rule)| {
                if expect_unused.contains(&(rule_name, SymbolKind::Rule)) {
                    None
                } else {
                    Some((rule_name, SymbolKind::Rule, rule.name.1))
                }
            })
            .chain(self.tokens.iter().enumerate().filter_map(|(tok_idx, tok)| {
                if expect_unused.contains(&(tok, SymbolKind::Token)) {
                    None
                } else {
                    Some((tok, SymbolKind::Token, self.spans[tok_idx]))
                }
            }))
            .filter_map(|(sym_name, kind, span)| {
                let used_sym = used_symbols.get(&(sym_name, kind));
                if used_sym.is_none() {
                    Some(YaccGrammarWarning {
                        kind: YaccGrammarWarningKind::UnusedSymbol,
                        spans: vec![span],
                    })
                } else {
                    None
                }
            })
            .collect::<Vec<_>>()
            .into_iter()
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
        grm.add_prod("B".to_string(), vec![], None, None);
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
        grm.add_prod("A".to_string(), vec![], None, None);
        assert!(grm.complete_and_validate().is_ok());
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
        assert!(grm.complete_and_validate().is_ok());
    }

    #[test]
    fn test_invalid_rule_ref() {
        let mut grm = GrammarAST::new();
        let empty_span = Span::new(0, 0);
        grm.start = Some(("A".to_string(), empty_span));
        grm.add_rule(("A".to_string(), empty_span), None);
        grm.add_prod("A".to_string(), vec![rule("B")], None, None);
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
        grm.add_prod("A".to_string(), vec![token("b")], None, None);
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
        grm.add_prod("A".to_string(), vec![rule("b")], None, None);
        assert!(grm.complete_and_validate().is_err());
    }

    #[test]
    fn test_invalid_token_ref() {
        let mut grm = GrammarAST::new();
        let empty_span = Span::new(0, 0);
        grm.start = Some(("A".to_string(), empty_span));
        grm.add_rule(("A".to_string(), empty_span), None);
        grm.add_prod("A".to_string(), vec![token("b")], None, None);
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
        grm.add_prod("A".to_string(), vec![rule("b"), token("b")], None, None);
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
        let empty_span = Span::new(0, 0);
        grm.start = Some(("A".to_string(), empty_span));
        grm.add_rule(("A".to_string(), empty_span), None);
        grm.add_prod("A".to_string(), vec![], None, None);
        grm.epp
            .insert("k".to_owned(), (empty_span, ("v".to_owned(), empty_span)));
        match grm.complete_and_validate() {
            Err(YaccGrammarError {
                kind: YaccGrammarErrorKind::UnknownEPP(_),
                ..
            }) => (),
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
}
