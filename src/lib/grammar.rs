use std::collections::HashMap;

use ast;

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

custom_derive! {
    /// A type specifically for production indices (e.g. a rule "E::=A|B" would
    /// have two productions for the single rule E).
    #[derive(Clone, Copy, Debug, Eq, Hash, NewtypeFrom, PartialEq, PartialOrd)]
    pub struct PIdx(usize);
}
custom_derive! {
    /// A type specifically for rule indices.
    #[derive(Clone, Copy, Debug, Eq, Hash, NewtypeFrom, PartialEq)]
    pub struct RIdx(usize);
}
custom_derive! {
    /// A type specifically for symbol indices (within a production).
    #[derive(Clone, Copy, Debug, Eq, Hash, NewtypeFrom, PartialEq, PartialOrd)]
    pub struct SIdx(usize);
}
custom_derive! {
    /// A type specifically for token indices.
    #[derive(Clone, Copy, Debug, Eq, Hash, NewtypeFrom, PartialEq)]
    pub struct TIdx(usize);
}

pub struct Grammar {
    /// A mapping from RIdx -> String.
    pub nonterminal_names: Vec<String>,
    pub nonterms_len: usize,
    /// A mapping from TIdx -> String.
    pub terminal_names: Vec<String>,
    /// A mapping from TIdx -> Option<Precedence>
    pub terminal_precs: Vec<Option<Precedence>>,
    pub terms_len: usize,
    /// Which production is the sole production of the start rule?
    pub start_prod: PIdx,
    /// The offset of the EOF terminal.
    pub end_term: TIdx,
    /// A mapping from rules to their productions. Note that 2) the order of rules is identical to
    /// that of `nonterminal_names' 2) every rule will have at least 1 production 3) productions
    /// are not necessarily stored sequentially.
    pub rules_prods: Vec<Vec<PIdx>>,
    /// A list of all productions.
    prods: Vec<Vec<Symbol>>,
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

impl Grammar {
    /// Translate a `GrammarAST` into a grammar. This function is akin to the part a traditional
    /// compiler that takes in an AST and converts it into a binary.
    ///
    /// As we're compiling the `GrammarAST` into a `Grammar` we do two extra things:
    ///   1) Add a new start rule (which we'll refer to as "^", though the actual name is a fresh name
    ///      that is guaranteed to be unique) that references the user defined start rule.
    ///   2) Add a new end terminal (which we'll refer to as "$", though the actual name is a fresh
    ///      name that is guaranteed to be unique).
    /// So, if the user's start rule is S, we add a nonterminal with a single production:
    ///   ^ : S '$';
    pub fn new(ast: &ast::GrammarAST) -> Grammar {
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
        while ast.tokens.iter().any(|x| x == &end_term) {
            end_term = end_term + END_TERM;
        }

        let mut nonterm_names: Vec<String> = Vec::with_capacity(ast.rules.len() + 1);
        nonterm_names.push(start_nonterm.clone());
        for k in ast.rules.keys() { nonterm_names.push(k.clone()); }
        nonterm_names.sort_by(|a, b| a.to_lowercase().cmp(&b.to_lowercase()));
        let mut rules_prods:Vec<Vec<PIdx>> = Vec::with_capacity(nonterm_names.len());
        let mut nonterm_map = HashMap::<String, RIdx>::new();
        for (i, v) in nonterm_names.iter().enumerate() {
            rules_prods.push(Vec::new());
            nonterm_map.insert(v.clone(), RIdx(i));
        }
        let mut term_names: Vec<String> = Vec::with_capacity(ast.tokens.len() + 1);
        let mut term_precs: Vec<Option<Precedence>> = Vec::with_capacity(ast.tokens.len() + 1);
        term_names.push(end_term.clone());
        term_precs.push(None);
        for k in &ast.tokens {
            term_names.push(k.clone());
            term_precs.push(ast.precs.get(k).map(|p| *p));
        }
        let mut terminal_map = HashMap::<String, TIdx>::new();
        for (i, v) in term_names.iter().enumerate() {
            terminal_map.insert(v.clone(), TIdx(i));
        }

        let mut prods                               = Vec::new();
        let mut prod_precs: Vec<Option<Precedence>> = Vec::new();
        for astrulename in &nonterm_names {
            if astrulename == &start_nonterm {
                rules_prods.get_mut(usize::from(nonterm_map[&start_nonterm])).unwrap().push(prods.len().into());
                let start_prod = vec![Symbol::Nonterminal(nonterm_map[ast.start.as_ref().unwrap()])];
                prods.push(start_prod);
                prod_precs.push(None);
                continue;
            }
            let astrule = &ast.rules[astrulename];
            let mut rule = rules_prods.get_mut(usize::from(nonterm_map[&astrule.name])).unwrap();
            for astprod in &astrule.productions {
                let mut prod = Vec::with_capacity(astprod.len());
                let mut prec = None;
                for astsym in astprod.iter() {
                    let sym = match *astsym {
                        ast::Symbol::Nonterminal(ref n) =>
                            Symbol::Nonterminal(nonterm_map[n]),
                        ast::Symbol::Terminal(ref n) =>
                            Symbol::Terminal(terminal_map[n])
                    };
                    prod.push(sym);
                }
                if prec.is_none() {
                    for astsym in astprod.iter().rev() {
                        if let ast::Symbol::Terminal(ref n) = *astsym {
                            if let Some(p) = ast.precs.get(n) {
                                prec = Some(*p);
                            }
                            break;
                        }
                    }
                }
                (*rule).push(prods.len().into());
                prods.push(prod);
                prod_precs.push(prec);
            }
        }

        Grammar{
            nonterms_len:      nonterm_names.len(),
            nonterminal_names: nonterm_names,
            terms_len:         term_names.len(),
            terminal_names:    term_names,
            terminal_precs:    term_precs,
            start_prod:        rules_prods[usize::from(nonterm_map[&start_nonterm])][0],
            end_term:          terminal_map[&end_term],
            rules_prods:       rules_prods,
            prods:             prods,
            prod_precs:        prod_precs
        }
    }

    /// Return the rule index of the production `i`.
    pub fn prod_to_rule_idx(&self, i: PIdx) -> RIdx {
        for (j, rule) in self.rules_prods.iter().enumerate() {
            if rule.iter().position(|x| *x == i).is_some() {
                return RIdx(j);
            }
        }
        panic!("Invalid index {:?}", i);
    }

    /// Get the sequence of symbols for production `i`.
    pub fn get_prod(&self, i: PIdx) -> Option<&[Symbol]> {
        self.prods.get(usize::from(i)).map_or(None, |x| Some(x))
    }

    pub fn prods_len(&self) -> usize {
        self.prods.len()
    }

    /// Return the rule name for rule `i`.
    pub fn get_rule_name(&self, i: RIdx) -> Option<&str> {
        self.nonterminal_names.get(usize::from(i)).map_or(None, |x| Some(&x))
    }
}

#[cfg(test)]
impl Grammar {
    /// Map a nonterminal name to the corresponding rule offset.
    pub fn nonterminal_off(&self, n: &str) -> RIdx {
        RIdx(self.nonterminal_names.iter().position(|x| x == n).unwrap())
    }

    /// Map a terminal name to the corresponding terminal offset.
    pub fn terminal_off(&self, n: &str) -> TIdx {
        TIdx(self.terminal_names.iter().position(|x| x == n).unwrap())
    }

    /// Map a production number to a rule name. Note: this has a worst case of O(n * m) where n is
    /// the number of rules in the grammar and m the total number of productions.
    pub fn prod_to_term_name(&self, i: PIdx) -> String {
        for (j, rule) in self.rules_prods.iter().enumerate() {
            if rule.iter().position(|x| *x == i).is_some() {
                return self.nonterminal_names[j].clone();
            }
        }
        panic!("Invalid index {}", usize::from(i));
    }
}


#[cfg(test)]
mod test {
    use super::{AssocKind, Grammar, PIdx, Precedence, Symbol};
    use yacc_parser::parse_yacc;

    #[test]
    fn test_minimal() {
        let ast = parse_yacc(&"%start R %token T %% R: 'T';".to_string()).unwrap();
        let grm = Grammar::new(&ast);

        assert_eq!(grm.start_prod, PIdx(0));
        grm.nonterminal_off("^");
        grm.nonterminal_off("R");
        grm.terminal_off("$");
        grm.terminal_off("T");

        assert_eq!(grm.rules_prods, vec![vec![PIdx(0)], vec![PIdx(1)]]);
        let start_prod = grm.get_prod(grm.rules_prods[usize::from(grm.nonterminal_off("^"))][0]).unwrap();
        assert_eq!(*start_prod, [Symbol::Nonterminal(grm.nonterminal_off("R"))]);
        let r_prod = grm.get_prod(grm.rules_prods[usize::from(grm.nonterminal_off("R"))][0]).unwrap();
        assert_eq!(*r_prod, [Symbol::Terminal(grm.terminal_off("T"))]);
    }

    #[test]
    fn test_rule_ref() {
        let ast = parse_yacc(&"%start R %token T %% R : S; S: 'T';".to_string()).unwrap();
        let grm = Grammar::new(&ast);

        grm.nonterminal_off("^");
        grm.nonterminal_off("R");
        grm.nonterminal_off("S");
        grm.terminal_off("$");
        grm.terminal_off("T");

        assert_eq!(grm.rules_prods, vec![vec![PIdx(0)], vec![PIdx(1)], vec![PIdx(2)]]);
        let start_prod = grm.get_prod(grm.rules_prods[usize::from(grm.nonterminal_off("^"))][0]).unwrap();
        assert_eq!(*start_prod, [Symbol::Nonterminal(grm.nonterminal_off("R"))]);
        let r_prod = grm.get_prod(grm.rules_prods[usize::from(grm.nonterminal_off("R"))][0]).unwrap();
        assert_eq!(r_prod.len(), 1);
        assert_eq!(r_prod[0], Symbol::Nonterminal(grm.nonterminal_off("S")));
        let s_prod = grm.get_prod(grm.rules_prods[usize::from(grm.nonterminal_off("S"))][0]).unwrap();
        assert_eq!(s_prod.len(), 1);
        assert_eq!(s_prod[0], Symbol::Terminal(grm.terminal_off("T")));
    }

    #[test]
    fn test_long_prod() {
        let ast = parse_yacc(&"%start R %token T1 T2 %% R : S 'T1' S; S: 'T2';".to_string()).unwrap();
        let grm = Grammar::new(&ast);

        grm.nonterminal_off("^");
        grm.nonterminal_off("R");
        grm.nonterminal_off("S");
        grm.terminal_off("$");
        grm.terminal_off("T1");
        grm.terminal_off("T2");

        assert_eq!(grm.rules_prods, vec![vec![PIdx(0)], vec![PIdx(1)], vec![PIdx(2)]]);
        let start_prod = grm.get_prod(grm.rules_prods[usize::from(grm.nonterminal_off("^"))][0]).unwrap();
        assert_eq!(*start_prod, [Symbol::Nonterminal(grm.nonterminal_off("R"))]);
        let r_prod = grm.get_prod(grm.rules_prods[usize::from(grm.nonterminal_off("R"))][0]).unwrap();
        assert_eq!(r_prod.len(), 3);
        assert_eq!(r_prod[0], Symbol::Nonterminal(grm.nonterminal_off("S")));
        assert_eq!(r_prod[1], Symbol::Terminal(grm.terminal_off("T1")));
        assert_eq!(r_prod[2], Symbol::Nonterminal(grm.nonterminal_off("S")));
        let s_prod = grm.get_prod(grm.rules_prods[usize::from(grm.nonterminal_off("S"))][0]).unwrap();
        assert_eq!(s_prod.len(), 1);
        assert_eq!(s_prod[0], Symbol::Terminal(grm.terminal_off("T2")));
    }

    #[test]
    fn test_left_right_nonassoc_precs() {
        let grm = Grammar::new(&parse_yacc(&"
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
