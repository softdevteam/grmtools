use std::collections::HashMap;

use grammar_ast;

/// A type specifically for nonterminal indices (i.e. corresponding to a rule
/// name).
pub type NIdx = i32;
/// A type specifically for alternative indices (e.g. a rule "E::=A|B" would
/// have two alternatives for the single rule E).
pub type AIdx = i32;
/// A type specifically for symbol indices.
pub type TIdx = i32;

pub struct Grammar {
    pub nonterminal_names: Vec<String>,
    pub terminal_names: Vec<String>,
    pub start_rule: NIdx,
    pub rules_alts: Vec<Vec<AIdx>>,
    pub alts: Vec<Vec<Symbol>>,
    //pub alts_rules: HashMap<AIdx, NIdx>
}

#[derive(Clone, Debug, Hash, Eq, PartialEq)]
pub enum Symbol {
    Nonterminal(NIdx),
    Terminal(TIdx)
}

impl Grammar {
    // For testing purposes only
    pub fn nonterminal_off(&self, n: &str) -> AIdx {
        self.nonterminal_names.iter().position(|x| x == n).unwrap() as NIdx
    }

    // For testing purposes only
    pub fn terminal_off(&self, n: &str) -> NIdx {
        self.terminal_names.iter().position(|x| x == n).unwrap() as NIdx
    }
}

pub fn ast_to_grammar(ast: &grammar_ast::GrammarAST) -> Grammar {
    // The user is expected to have called validate before calling this function.
    assert!(ast.validate().is_ok());

    let nonterminal_names   = ast.rules.keys().map(|x| x.clone()).collect::<Vec<String>>();
    let mut rules_alts:Vec<Vec<AIdx>> = Vec::with_capacity(nonterminal_names.len());
    let mut nonterminal_map = HashMap::<String, NIdx>::new();
    for (i, v) in nonterminal_names.iter().enumerate() {
        rules_alts.push(Vec::new());
        nonterminal_map.insert(v.clone(), i as NIdx);
    }
    let terminal_names      = ast.tokens.iter().map(|x| x.clone()).collect::<Vec<String>>();
    let mut terminal_map    = HashMap::<String, TIdx>::new();
    for (i, v) in terminal_names.iter().enumerate() {
        terminal_map.insert(v.clone(), i as TIdx);
    }

    let mut alts = Vec::new();
    for astrule in ast.rules.values() {
        let mut rule = rules_alts.get_mut(*nonterminal_map.get(&astrule.name).unwrap() as usize).unwrap();
        for astalt in astrule.alternatives.iter() {
            let mut alt = Vec::with_capacity(astalt.len());
            for astsym in astalt.iter() {
                let sym = match astsym {
                    &grammar_ast::Symbol::Nonterminal(ref n) =>
                        Symbol::Nonterminal(*nonterminal_map.get(n).unwrap()),
                    &grammar_ast::Symbol::Terminal(ref n) =>
                        Symbol::Terminal(*terminal_map.get(n).unwrap())
                };
                alt.push(sym);
            }
            (*rule).push(alts.len() as AIdx);
            alts.push(alt);
        }
    }

    Grammar{
        nonterminal_names: nonterminal_names,
        terminal_names:    terminal_names,
        start_rule:        *nonterminal_map.get(ast.start.as_ref().unwrap()).unwrap() as NIdx,
        rules_alts:        rules_alts,
        alts:              alts,
    }
}
