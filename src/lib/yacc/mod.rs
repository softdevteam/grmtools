// Copyright (c) 2017 King's College London
// created by the Software Development Team <http://soft-dev.org/>
//
// The Universal Permissive License (UPL), Version 1.0
//
// Subject to the condition set forth below, permission is hereby granted to any person obtaining a
// copy of this software, associated documentation and/or data (collectively the "Software"), free
// of charge and under any and all copyright rights in the Software, and any and all patent rights
// owned or freely licensable by each licensor hereunder covering either (i) the unmodified
// Software as contributed to or provided by such licensor, or (ii) the Larger Works (as defined
// below), to deal in both
//
// (a) the Software, and
// (b) any piece of software and/or hardware listed in the lrgrwrks.txt file
// if one is included with the Software (each a "Larger Work" to which the Software is contributed
// by such licensors),
//
// without restriction, including without limitation the rights to copy, create derivative works
// of, display, perform, and distribute the Software and make, use, sell, offer for sale, import,
// export, have made, and have sold the Software and the Larger Work(s), and to sublicense the
// foregoing rights on either these or other terms.
//
// This license is subject to the following condition: The above copyright notice and either this
// complete permission notice or at a minimum a reference to the UPL must be included in all copies
// or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING
// BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
// NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
// DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

use std::collections::HashMap;

use super::{NTIdx, PIdx, SIdx, Symbol, TIdx};

mod ast;
mod parser;

const START_NONTERM: &'static str = "^";
const END_TERM     : &'static str = "$";

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

pub struct YaccGrammar {
    /// How many nonterminals does this grammar have?
    pub nonterms_len: usize,
    /// A mapping from NTIdx -> String.
    pub nonterminal_names: Vec<String>,
    /// A mapping from TIdx -> String.
    pub terminal_names: Vec<String>,
    /// A mapping from TIdx -> Option<Precedence>
    pub terminal_precs: Vec<Option<Precedence>>,
    /// How many terminals does this grammar have?
    pub terms_len: usize,
    /// The offset of the EOF terminal.
    pub end_term: TIdx,
    /// How many productions does this grammar have?
    pub prods_len: usize,
    /// Which production is the sole production of the start rule?
    pub start_prod: PIdx,
    /// A list of all productions.
    pub prods: Vec<Vec<Symbol>>,
    /// A mapping from rules to their productions. Note that 1) the order of rules is identical to
    /// that of `nonterminal_names' 2) every rule will have at least 1 production 3) productions
    /// are not necessarily stored sequentially.
    pub rules_prods: Vec<Vec<PIdx>>,
    /// A mapping from productions to their corresponding rule indexes.
    pub prods_rules: Vec<NTIdx>,
    /// The precedence of each production.
    pub prod_precs: Vec<Option<Precedence>>
}


impl YaccGrammar {
    /// Translate a `GrammarAST` into a `YaccGrammar`. This function is akin to the part a traditional
    /// compiler that takes in an AST and converts it into a binary.
    ///
    /// As we're compiling the `GrammarAST` into a `Grammar` we do two extra things:
    ///   1) Add a new start rule (which we'll refer to as "^", though the actual name is a fresh name
    ///      that is guaranteed to be unique) that references the user defined start rule.
    ///   2) Add a new end terminal (which we'll refer to as "$", though the actual name is a fresh
    ///      name that is guaranteed to be unique).
    /// So, if the user's start rule is S, we add a nonterminal with a single production `^ : S '$';`.
    pub fn new(ast: &ast::GrammarAST) -> YaccGrammar {
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
        let mut nonterm_map = HashMap::<String, NTIdx>::new();
        for (i, v) in nonterm_names.iter().enumerate() {
            rules_prods.push(Vec::new());
            nonterm_map.insert(v.clone(), NTIdx(i));
        }
        let mut term_names: Vec<String> = Vec::with_capacity(ast.tokens.len() + 1);
        let mut term_precs: Vec<Option<Precedence>> = Vec::with_capacity(ast.tokens.len() + 1);
        term_names.push(end_term.clone());
        term_precs.push(None);
        for k in &ast.tokens {
            term_names.push(k.clone());
            term_precs.push(ast.precs.get(k).cloned());
        }
        let mut terminal_map = HashMap::<String, TIdx>::new();
        for (i, v) in term_names.iter().enumerate() {
            terminal_map.insert(v.clone(), TIdx(i));
        }

        let mut prods                               = Vec::new();
        let mut prod_precs: Vec<Option<Precedence>> = Vec::new();
        let mut prods_rules = Vec::new();
        for astrulename in &nonterm_names {
            let rule_idx = nonterm_map[astrulename];
            if astrulename == &start_nonterm {
                rules_prods.get_mut(usize::from(nonterm_map[&start_nonterm])).unwrap().push(prods.len().into());
                let start_prod = vec![Symbol::Nonterminal(nonterm_map[ast.start.as_ref().unwrap()])];
                prods.push(start_prod);
                prod_precs.push(None);
                prods_rules.push(rule_idx);
                continue;
            }
            let astrule = &ast.rules[astrulename];
            let mut rule = &mut rules_prods[usize::from(rule_idx)];
            for astprod in &astrule.productions {
                let mut prod = Vec::with_capacity(astprod.symbols.len());
                for astsym in &astprod.symbols {
                    let sym = match *astsym {
                        ast::Symbol::Nonterminal(ref n) =>
                            Symbol::Nonterminal(nonterm_map[n]),
                        ast::Symbol::Terminal(ref n) =>
                            Symbol::Terminal(terminal_map[n])
                    };
                    prod.push(sym);
                }
                let mut prec = None;
                if let Some(ref n) = astprod.precedence {
                    prec = Some(ast.precs[n]);
                } else {
                    for astsym in astprod.symbols.iter().rev() {
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
                prods_rules.push(rule_idx);
            }
        }

        YaccGrammar{
            nonterms_len:      nonterm_names.len(),
            nonterminal_names: nonterm_names,
            terms_len:         term_names.len(),
            end_term:          terminal_map[&end_term],
            terminal_names:    term_names,
            terminal_precs:    term_precs,
            prods_len:         prods.len(),
            start_prod:        rules_prods[usize::from(nonterm_map[&start_nonterm])][0],
            rules_prods:       rules_prods,
            prods_rules:       prods_rules,
            prods:             prods,
            prod_precs:        prod_precs
        }
    }

    /// Return the productions for nonterminal `i` or None if it doesn't exist.
    pub fn nonterm_to_prods(&self, i: NTIdx) -> Option<&[PIdx]> {
        self.rules_prods.get(usize::from(i)).map_or(None, |x| Some(x))
    }

    /// Return the name of nonterminal `i` or None if it doesn't exist.
    pub fn nonterm_name(&self, i: NTIdx) -> Option<&str> {
        self.nonterminal_names.get(usize::from(i)).map_or(None, |x| Some(&x))
    }

    /// Return an iterator which produces (in no particular order) all this grammar's valid NTIdxs.
    pub fn iter_nonterm_idxs(&self) -> Box<Iterator<Item=NTIdx>> {
        Box::new((0..self.nonterms_len).map(NTIdx))
    }

    /// Get the sequence of symbols for production `i` or None if it doesn't exist.
    pub fn prod(&self, i: PIdx) -> Option<&[Symbol]> {
        self.prods.get(usize::from(i)).map_or(None, |x| Some(x))
    }

    /// Return the nonterm index of the production `i` or None if it doesn't exist.
    pub fn prod_to_nonterm(&self, i: PIdx) -> NTIdx {
        self.prods_rules[usize::from(i)]
    }

    /// Return the precedence of production `i` or None if it doesn't exist.
    pub fn prod_precedence(&self, i: PIdx) -> Option<Option<Precedence>> {
        self.prod_precs.get(usize::from(i)).map_or(None, |x| Some(*x))
    }

    /// Return the name of terminal `i` or None if it doesn't exist.
    pub fn term_name(&self, i: TIdx) -> Option<&str> {
        self.terminal_names.get(usize::from(i)).map_or(None, |x| Some(x))
    }

    /// Return the precedence of terminal `i` or None if it doesn't exist.
    pub fn term_precedence(&self, i: TIdx) -> Option<Option<Precedence>> {
        self.terminal_precs.get(usize::from(i)).map_or(None, |x| Some(*x))
    }

    /// Return an iterator which produces (in no particular order) all this grammar's valid TIdxs.
    pub fn iter_term_idxs(&self) -> Box<Iterator<Item=TIdx>> {
        Box::new((0..self.terms_len).map(TIdx))
    }
}

#[cfg(test)]
impl YaccGrammar {
    /// Map a nonterminal name to the corresponding rule offset.
    pub fn nonterminal_off(&self, n: &str) -> NTIdx {
        NTIdx(self.nonterminal_names.iter().position(|x| x == n).unwrap())
    }

    /// Map a terminal name to the corresponding terminal offset.
    pub fn terminal_off(&self, n: &str) -> TIdx {
        TIdx(self.terminal_names.iter().position(|x| x == n).unwrap())
    }

    /// Map a production number to a rule name.
    pub fn prod_to_term_name(&self, i: PIdx) -> &str {
        &self.nonterminal_names[usize::from(self.prod_to_nonterm(i))]
    }
}


#[cfg(test)]
mod test {
    use super::{AssocKind, YaccGrammar, NTIdx, PIdx, Precedence, Symbol, TIdx};
    use yacc::parser::parse_yacc;

    #[test]
    fn test_minimal() {
        let ast = parse_yacc(&"%start R %token T %% R: 'T';".to_string()).unwrap();
        let grm = YaccGrammar::new(&ast);

        assert_eq!(grm.start_prod, PIdx(0));
        grm.nonterminal_off("^");
        grm.nonterminal_off("R");
        grm.terminal_off("$");
        grm.terminal_off("T");

        assert_eq!(grm.rules_prods, vec![vec![PIdx(0)], vec![PIdx(1)]]);
        let start_prod = grm.prod(grm.rules_prods[usize::from(grm.nonterminal_off("^"))][0]).unwrap();
        assert_eq!(*start_prod, [Symbol::Nonterminal(grm.nonterminal_off("R"))]);
        let r_prod = grm.prod(grm.rules_prods[usize::from(grm.nonterminal_off("R"))][0]).unwrap();
        assert_eq!(*r_prod, [Symbol::Terminal(grm.terminal_off("T"))]);
        assert_eq!(grm.prods_rules, vec![NTIdx(0), NTIdx(1)]);

        assert_eq!(grm.iter_term_idxs().collect::<Vec<TIdx>>(), vec![TIdx(0), TIdx(1)]);
        assert_eq!(grm.iter_nonterm_idxs().collect::<Vec<NTIdx>>(), vec![NTIdx(0), NTIdx(1)]);
    }

    #[test]
    fn test_rule_ref() {
        let ast = parse_yacc(&"%start R %token T %% R : S; S: 'T';".to_string()).unwrap();
        let grm = YaccGrammar::new(&ast);

        grm.nonterminal_off("^");
        grm.nonterminal_off("R");
        grm.nonterminal_off("S");
        grm.terminal_off("$");
        grm.terminal_off("T");

        assert_eq!(grm.rules_prods, vec![vec![PIdx(0)], vec![PIdx(1)], vec![PIdx(2)]]);
        let start_prod = grm.prod(grm.rules_prods[usize::from(grm.nonterminal_off("^"))][0]).unwrap();
        assert_eq!(*start_prod, [Symbol::Nonterminal(grm.nonterminal_off("R"))]);
        let r_prod = grm.prod(grm.rules_prods[usize::from(grm.nonterminal_off("R"))][0]).unwrap();
        assert_eq!(r_prod.len(), 1);
        assert_eq!(r_prod[0], Symbol::Nonterminal(grm.nonterminal_off("S")));
        let s_prod = grm.prod(grm.rules_prods[usize::from(grm.nonterminal_off("S"))][0]).unwrap();
        assert_eq!(s_prod.len(), 1);
        assert_eq!(s_prod[0], Symbol::Terminal(grm.terminal_off("T")));
    }

    #[test]
    fn test_long_prod() {
        let ast = parse_yacc(&"%start R %token T1 T2 %% R : S 'T1' S; S: 'T2';".to_string()).unwrap();
        let grm = YaccGrammar::new(&ast);

        grm.nonterminal_off("^");
        grm.nonterminal_off("R");
        grm.nonterminal_off("S");
        grm.terminal_off("$");
        grm.terminal_off("T1");
        grm.terminal_off("T2");

        assert_eq!(grm.rules_prods, vec![vec![PIdx(0)], vec![PIdx(1)], vec![PIdx(2)]]);
        assert_eq!(grm.prods_rules, vec![NTIdx(0), NTIdx(1), NTIdx(2)]);
        let start_prod = grm.prod(grm.rules_prods[usize::from(grm.nonterminal_off("^"))][0]).unwrap();
        assert_eq!(*start_prod, [Symbol::Nonterminal(grm.nonterminal_off("R"))]);
        let r_prod = grm.prod(grm.rules_prods[usize::from(grm.nonterminal_off("R"))][0]).unwrap();
        assert_eq!(r_prod.len(), 3);
        assert_eq!(r_prod[0], Symbol::Nonterminal(grm.nonterminal_off("S")));
        assert_eq!(r_prod[1], Symbol::Terminal(grm.terminal_off("T1")));
        assert_eq!(r_prod[2], Symbol::Nonterminal(grm.nonterminal_off("S")));
        let s_prod = grm.prod(grm.rules_prods[usize::from(grm.nonterminal_off("S"))][0]).unwrap();
        assert_eq!(s_prod.len(), 1);
        assert_eq!(s_prod[0], Symbol::Terminal(grm.terminal_off("T2")));
    }


    #[test]
    fn test_prods_rules() {
        let grm = YaccGrammar::new(&parse_yacc(&"
            %start A
            %%
            A: B
             | C;
            B: 'x';
            C: 'y'
             | 'z';
          ".to_string()).unwrap());

        assert_eq!(grm.prods_rules, vec![NTIdx(0), NTIdx(1), NTIdx(1), NTIdx(2), NTIdx(3), NTIdx(3)]);
    }

    #[test]
    fn test_left_right_nonassoc_precs() {
        let grm = YaccGrammar::new(&parse_yacc(&"
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
          ").unwrap());

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

    #[test]
    fn test_prec_override() {
        let grm = YaccGrammar::new(&parse_yacc(&"
            %start expr
            %left '+' '-'
            %left '*' '/'
            %%
            expr : expr '+' expr
                 | expr '-' expr
                 | expr '*' expr
                 | expr '/' expr
                 | '-'  expr %prec '*'
                 | 'id' ;
        ").unwrap());
        assert_eq!(grm.prod_precs.len(), 7);
        assert_eq!(grm.prod_precs[0], None);
        assert_eq!(grm.prod_precs[1].unwrap(), Precedence{level: 0, kind: AssocKind::Left});
        assert_eq!(grm.prod_precs[2].unwrap(), Precedence{level: 0, kind: AssocKind::Left});
        assert_eq!(grm.prod_precs[3].unwrap(), Precedence{level: 1, kind: AssocKind::Left});
        assert_eq!(grm.prod_precs[4].unwrap(), Precedence{level: 1, kind: AssocKind::Left});
        assert_eq!(grm.prod_precs[5].unwrap(), Precedence{level: 1, kind: AssocKind::Left});
        assert!(grm.prod_precs[6].is_none());
    }
}
