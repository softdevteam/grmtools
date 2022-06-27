use std::{collections::HashMap, fmt};

use indexmap::{IndexMap, IndexSet};

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
                    span: Span::new(0, 0),
                });
            }
            Some((ref s, span)) => {
                if !self.rules.contains_key(s) {
                    return Err(YaccGrammarError {
                        kind: YaccGrammarErrorKind::InvalidStartRule(s.clone()),
                        span,
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
                            span: Span::new(0, 0),
                        });
                    }
                    if !self.precs.contains_key(n) {
                        return Err(YaccGrammarError {
                            kind: YaccGrammarErrorKind::NoPrecForToken(n.clone()),
                            span: Span::new(0, 0),
                        });
                    }
                }
                for sym in &prod.symbols {
                    match *sym {
                        Symbol::Rule(ref name, span) => {
                            if !self.rules.contains_key(name) {
                                return Err(YaccGrammarError {
                                    kind: YaccGrammarErrorKind::UnknownRuleRef(name.clone()),
                                    span,
                                });
                            }
                        }
                        Symbol::Token(ref name, span) => {
                            if !self.tokens.contains(name) {
                                return Err(YaccGrammarError {
                                    kind: YaccGrammarErrorKind::UnknownToken(name.clone()),
                                    span,
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
                span: Span::new(0, 0),
            });
        }
        Ok(())
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
