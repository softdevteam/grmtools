use std::collections::HashMap;

use grammar_ast;

pub const START_NONTERM: &'static str = "^";
pub const END_TERM     : &'static str = "$";

// A note on the terminology we use (since this isn't entirely consistent in the literature):
//   A symbol is either a nonterminal or a terminal.
//   A rule is a mapping from a nonterminal name to 1 or more productions (the latter of which is
//     often called 'alternatives').
//   A production is a possibly empty list of symbols.
//
// Because we're dealing with traditional LR grammars, every nonterminal name must have a
// corresponding rule; terminals are not required to appear in any production.
//
// The code also assumes that the start rule only has a single production. Since the code manually
// creates this start rule, this is a safe assumption.

/// A type specifically for production indices (e.g. a rule "E::=A|B" would
/// have two productions for the single rule E).
pub type PIdx = usize;
/// A type specifically for rule indices.
pub type RIdx = usize;
/// A type specifically for symbol indices (within a production).
pub type SIdx = usize;
/// A type specifically for token indices.
pub type TIdx = usize;

pub struct Grammar {
    /// A mapping from RIdx -> String.
    pub nonterminal_names: Vec<String>,
    pub nonterms_len: RIdx,
    /// A mapping from TIdx -> String.
    pub terminal_names: Vec<String>,
    /// A mapping from TIdx -> Option<Precedence>
    pub terminal_precs: Vec<Option<Precedence>>,
    pub terms_len: TIdx,
    /// Which production is the sole production of the start rule?
    pub start_prod: PIdx,
    /// The offset of the EOF terminal.
    pub end_term: TIdx,
    /// A mapping from rules to their productions. Note that 2) the order of rules is identical to
    /// that of `nonterminal_names' 2) every rule will have at least 1 production 3) productions
    /// are not necessarily stored sequentially.
    pub rules_prods: Vec<Vec<PIdx>>,
    /// A list of all productions.
    pub prods: Vec<Vec<Symbol>>,
    pub prod_precs: Vec<Option<Precedence>>
}

#[derive(Clone, Copy, Debug, Hash, Eq, PartialEq)]
pub enum Symbol {
    Nonterminal(RIdx),
    Terminal(TIdx)
}

pub type PrecedenceLevel = u64;
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Precedence {
    pub level: PrecedenceLevel,
    pub kind:  AssocKind
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum AssocKind {
    Left,
    Right,
    Nonassoc
}

#[cfg(test)]
impl Grammar {
    /// Map a nonterminal name to the corresponding rule offset.
    pub fn nonterminal_off(&self, n: &str) -> RIdx {
        self.nonterminal_names.iter().position(|x| x == n).unwrap()
    }

    /// Map a terminal name to the corresponding terminal offset.
    pub fn terminal_off(&self, n: &str) -> TIdx {
        self.terminal_names.iter().position(|x| x == n).unwrap()
    }

    /// Map a production number to a rule name. Note: this has a worst case of O(n * m) where n is
    /// the number of rules in the grammar and m the total number of productions.
    pub fn prod_to_term_name(&self, i: PIdx) -> String {
        for (j, rule) in self.rules_prods.iter().enumerate() {
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
/// So, if the user's start rule is S, we add a nonterminal with a single production:
///   ^ : S '$';
pub fn ast_to_grammar(ast: &grammar_ast::GrammarAST) -> Grammar {
    // The user is expected to have called validate before calling this function.
    debug_assert!(ast.validate().is_ok());

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
    nonterminal_names.sort_by(|a, b| a.to_lowercase().cmp(&b.to_lowercase()));
    let mut rules_prods:Vec<Vec<PIdx>> = Vec::with_capacity(nonterminal_names.len());
    let mut nonterminal_map = HashMap::<String, RIdx>::new();
    for (i, v) in nonterminal_names.iter().enumerate() {
        rules_prods.push(Vec::new());
        nonterminal_map.insert(v.clone(), i);
    }
    let mut terminal_names: Vec<String> = Vec::with_capacity(ast.tokens.len() + 1);
    let mut terminal_precs: Vec<Option<Precedence>> = Vec::with_capacity(ast.tokens.len() + 1);
    terminal_names.push(end_term.clone());
    terminal_precs.push(None);
    for k in ast.tokens.iter() {
        terminal_names.push(k.clone());
        terminal_precs.push(ast.precs.get(k).map(|p| *p));
    }
    let mut terminal_map = HashMap::<String, TIdx>::new();
    for (i, v) in terminal_names.iter().enumerate() {
        terminal_map.insert(v.clone(), i);
    }

    let mut prods                               = Vec::new();
    let mut prod_precs: Vec<Option<Precedence>> = Vec::new();
    for astrulename in nonterminal_names.iter() {
        if astrulename == &start_nonterm {
            rules_prods.get_mut(nonterminal_map[&start_nonterm]).unwrap().push(prods.len());
            let start_prod = vec![Symbol::Nonterminal(nonterminal_map[ast.start.as_ref().unwrap()])];
            prods.push(start_prod);
            prod_precs.push(None);
            continue;
        }
        let astrule = &ast.rules[astrulename];
        let mut rule = rules_prods.get_mut(nonterminal_map[&astrule.name]).unwrap();
        for astprod in astrule.productions.iter() {
            let mut prod = Vec::with_capacity(astprod.len());
            let mut prec = None;
            for astsym in astprod.iter() {
                let sym = match astsym {
                    &grammar_ast::Symbol::Nonterminal(ref n) =>
                        Symbol::Nonterminal(nonterminal_map[n]),
                    &grammar_ast::Symbol::Terminal(ref n) =>
                        Symbol::Terminal(terminal_map[n])
                };
                prod.push(sym);
            }
            if prec.is_none() {
                for astsym in astprod.iter().rev() {
                    if let &grammar_ast::Symbol::Terminal(ref n) = astsym {
                        if let Some(p) = ast.precs.get(n) {
                            prec = Some(*p);
                        }
                        break;
                    }
                }
            }
            (*rule).push(prods.len());
            prods.push(prod);
            prod_precs.push(prec);
        }
    }

    Grammar{
        nonterms_len:      nonterminal_names.len(),
        nonterminal_names: nonterminal_names,
        terms_len:         terminal_names.len(),
        terminal_names:    terminal_names,
        terminal_precs:    terminal_precs,
        start_prod:        rules_prods[nonterminal_map[&start_nonterm]][0],
        end_term:          terminal_map[&end_term],
        rules_prods:       rules_prods,
        prods:             prods,
        prod_precs:        prod_precs
    }
}

#[cfg(test)]
mod test {
    use super::{AssocKind, ast_to_grammar, Precedence, Symbol};
    use yacc::parse_yacc;

    #[test]
    fn test_minimal() {
        let ast = parse_yacc(&"%start R %token T %% R: 'T';".to_string()).unwrap();
        let grm = ast_to_grammar(&ast);

        assert_eq!(grm.start_prod, 0);
        grm.nonterminal_off("^");
        grm.nonterminal_off("R");
        grm.terminal_off("$");
        grm.terminal_off("T");

        assert_eq!(grm.rules_prods, vec![vec![0], vec![1]]);
        let start_prod = grm.prods.get(grm.rules_prods.get(grm.nonterminal_off("^")).unwrap()[0]).unwrap();
        assert_eq!(*start_prod, vec![Symbol::Nonterminal(grm.nonterminal_off("R"))]);
        let r_prod = grm.prods.get(grm.rules_prods.get(grm.nonterminal_off("R")).unwrap()[0] as
                                 usize).unwrap();
        assert_eq!(*r_prod, vec![Symbol::Terminal(grm.terminal_off("T"))]);
    }

    #[test]
    fn test_rule_ref() {
        let ast = parse_yacc(&"%start R %token T %% R : S; S: 'T';".to_string()).unwrap();
        let grm = ast_to_grammar(&ast);

        grm.nonterminal_off("^");
        grm.nonterminal_off("R");
        grm.nonterminal_off("S");
        grm.terminal_off("$");
        grm.terminal_off("T");

        assert_eq!(grm.rules_prods, vec![vec![0], vec![1], vec![2]]);
        let start_prod = grm.prods.get(grm.rules_prods.get(grm.nonterminal_off("^")).unwrap()[0]).unwrap();
        assert_eq!(*start_prod, vec![Symbol::Nonterminal(grm.nonterminal_off("R"))]);
        let r_prod = grm.prods.get(grm.rules_prods.get(grm.nonterminal_off("R")).unwrap()[0] as
                                 usize).unwrap();
        assert_eq!(r_prod.len(), 1);
        assert_eq!(r_prod[0], Symbol::Nonterminal(grm.nonterminal_off("S")));
        let s_prod = grm.prods.get(grm.rules_prods.get(grm.nonterminal_off("S")).unwrap()[0] as
                                 usize).unwrap();
        assert_eq!(s_prod.len(), 1);
        assert_eq!(s_prod[0], Symbol::Terminal(grm.terminal_off("T")));
    }

    #[test]
    fn test_long_prod() {
        let ast = parse_yacc(&"%start R %token T1 T2 %% R : S 'T1' S; S: 'T2';".to_string()).unwrap();
        let grm = ast_to_grammar(&ast);

        grm.nonterminal_off("^");
        grm.nonterminal_off("R");
        grm.nonterminal_off("S");
        grm.terminal_off("$");
        grm.terminal_off("T1");
        grm.terminal_off("T2");

        assert_eq!(grm.rules_prods, vec![vec![0], vec![1], vec![2]]);
        let start_prod = grm.prods.get(grm.rules_prods.get(grm.nonterminal_off("^")).unwrap()[0]).unwrap();
        assert_eq!(*start_prod, vec![Symbol::Nonterminal(grm.nonterminal_off("R"))]);
        let r_prod = grm.prods.get(grm.rules_prods.get(grm.nonterminal_off("R")).unwrap()[0] as
                                 usize).unwrap();
        assert_eq!(r_prod.len(), 3);
        assert_eq!(r_prod[0], Symbol::Nonterminal(grm.nonterminal_off("S")));
        assert_eq!(r_prod[1], Symbol::Terminal(grm.terminal_off("T1")));
        assert_eq!(r_prod[2], Symbol::Nonterminal(grm.nonterminal_off("S")));
        let s_prod = grm.prods.get(grm.rules_prods.get(grm.nonterminal_off("S")).unwrap()[0] as
                                 usize).unwrap();
        assert_eq!(s_prod.len(), 1);
        assert_eq!(s_prod[0], Symbol::Terminal(grm.terminal_off("T2")));
    }

    #[test]
    fn test_left_right_nonassoc_precs() {
        let grm = ast_to_grammar(&parse_yacc(&"
            %start Expr
            %right '='
            %left '+' '-'
            %left '/'
            %left '*'
            %nonassoc '~'
            %%
            Expr : Expr '=' Expr
                 | Expr '+' Expr
                 | Expr '-' Expr
                 | Expr '/' Expr
                 | Expr '*' Expr
                 | Expr '~' Expr
                 | 'id' ;
          ".to_string()).unwrap());

        assert_eq!(grm.prod_precs.len(), 8);
        assert_eq!(grm.prod_precs[0], None); 
        assert_eq!(grm.prod_precs[1].unwrap(), Precedence{level: 0, kind: AssocKind::Right});
        assert_eq!(grm.prod_precs[2].unwrap(), Precedence{level: 1, kind: AssocKind::Left});
        assert_eq!(grm.prod_precs[3].unwrap(), Precedence{level: 1, kind: AssocKind::Left});
        assert_eq!(grm.prod_precs[4].unwrap(), Precedence{level: 2, kind: AssocKind::Left});
        assert_eq!(grm.prod_precs[5].unwrap(), Precedence{level: 3, kind: AssocKind::Left});
        assert_eq!(grm.prod_precs[6].unwrap(), Precedence{level: 4, kind: AssocKind::Nonassoc});
        assert!(grm.prod_precs[7].is_none());
    }
}
