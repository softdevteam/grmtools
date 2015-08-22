use std::collections::HashMap;

use grammar_ast;

pub const START_NONTERM: &'static str = "^";
pub const END_TERM     : &'static str = "$";

/// A type specifically for nonterminal indices (i.e. corresponding to a rule
/// name).
pub type NIdx = usize;
/// A type specifically for alternative indices (e.g. a rule "E::=A|B" would
/// have two alternatives for the single rule E).
pub type AIdx = usize;
/// A type specifically for symbol indices (within an alternative).
pub type SIdx = usize;
/// A type specifically for token indices.
pub type TIdx = usize;

pub struct Grammar {
    pub nonterms_len: NIdx,
    pub nonterminal_names: Vec<String>,
    pub terms_len: TIdx,
    pub terminal_names: Vec<String>,
    pub start_rule: NIdx,
    pub end_term: TIdx,
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
        self.nonterminal_names.iter().position(|x| x == n).unwrap()
    }

    // For testing purposes only
    pub fn terminal_off(&self, n: &str) -> NIdx {
        self.terminal_names.iter().position(|x| x == n).unwrap()
    }

    // For testing purposes only
    pub fn alt_to_term_name(&self, i: AIdx) -> String {
        for (j, rule) in self.rules_alts.iter().enumerate() {
            if rule.iter().position(|x| *x == i).is_some() {
                return self.nonterminal_names[j].clone();
            }
        }
        panic!("Invalid index {}", i);
    }
}

/// Translate a `GrammarAST` into a grammar. This function is akin to the part a traditional
/// compiler that takes in an AST and converts it into a binary.
///
/// As we're compiling the GrammarAST into a Grammar we do two extra things:
///   1) Add a new start rule (which we'll refer to as "^", though the actual name is a fresh name
///      that is guaranteed to be unique) that references the user defined start rule. 
///   2) Add a new end terminal (which we'll refer to as "$", though the actual name is a fresh
///      name that is guaranteed to be unique).
/// So, if the user's start rule is S, we add a nonterminal with a single alternative:
///   ^ : S '$';
pub fn ast_to_grammar(ast: &grammar_ast::GrammarAST) -> Grammar {
    // The user is expected to have called validate before calling this function.
    assert!(ast.validate().is_ok());

    // First of all generate guaranteed unique start nonterm and end term names. We simply keep
    // making the string longer until we've hit something unique (at the very worst, this will
    // require looping for as many times as there are nonterminals / terminals).

    let mut start_nonterm = START_NONTERM.to_string();
    while ast.rules.get(&start_nonterm).is_some() {
        start_nonterm = start_nonterm + START_NONTERM;
    }

    let mut end_term = END_TERM.to_string();
    while ast.tokens.iter().position(|x| x == &end_term).is_some() {
        end_term = end_term + END_TERM;
    }

    let mut nonterminal_names: Vec<String> = Vec::with_capacity(ast.rules.len() + 1);
    nonterminal_names.push(start_nonterm.clone());
    for k in ast.rules.keys() { nonterminal_names.push(k.clone()); }
    let mut rules_alts:Vec<Vec<AIdx>> = Vec::with_capacity(nonterminal_names.len());
    let mut nonterminal_map = HashMap::<String, NIdx>::new();
    for (i, v) in nonterminal_names.iter().enumerate() {
        rules_alts.push(Vec::new());
        nonterminal_map.insert(v.clone(), i);
    }
    let mut terminal_names: Vec<String> = Vec::with_capacity(ast.tokens.len() + 1);
    terminal_names.push(end_term.clone());
    for k in ast.tokens.iter() { terminal_names.push(k.clone()); }
    let mut terminal_map = HashMap::<String, TIdx>::new();
    for (i, v) in terminal_names.iter().enumerate() {
        terminal_map.insert(v.clone(), i);
    }

    let mut alts = Vec::new();
    let start_alt = vec![
      Symbol::Nonterminal(nonterminal_map[ast.start.as_ref().unwrap()]),
      Symbol::Terminal(terminal_map[&end_term])
    ];
    alts.push(start_alt);
    rules_alts.get_mut(nonterminal_map[&start_nonterm]).unwrap().push(0);
    for astrule in ast.rules.values() {
        let mut rule = rules_alts.get_mut(nonterminal_map[&astrule.name]).unwrap();
        for astalt in astrule.alternatives.iter() {
            let mut alt = Vec::with_capacity(astalt.len());
            for astsym in astalt.iter() {
                let sym = match astsym {
                    &grammar_ast::Symbol::Nonterminal(ref n) =>
                        Symbol::Nonterminal(nonterminal_map[n]),
                    &grammar_ast::Symbol::Terminal(ref n) =>
                        Symbol::Terminal(terminal_map[n])
                };
                alt.push(sym);
            }
            (*rule).push(alts.len());
            alts.push(alt);
        }
    }

    Grammar{
        nonterms_len:      nonterminal_names.len(),
        nonterminal_names: nonterminal_names,
        terms_len:         terminal_names.len(),
        terminal_names:    terminal_names,
        start_rule:        nonterminal_map[&start_nonterm],
        end_term:          terminal_map[&end_term],
        rules_alts:        rules_alts,
        alts:              alts,
    }
}
