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
use std::fmt;

use {Grammar, NTIdx, PIdx, Symbol, TIdx};
use super::YaccKind;

const START_NONTERM         : &'static str = "^";
const IMPLICIT_NONTERM      : &'static str = "~";
const IMPLICIT_START_NONTERM: &'static str = "^~";

use yacc::ast;
use yacc::ast::GrammarValidationError;
use yacc::parser::YaccParserError;

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

/// Representation of a `YaccGrammar`. This struct makes one important guarantee: all of its
/// terminals will be consecutively, monotonically numbered from `0 .. terms_len()`. In other words,
/// if this struct has 3 terminals, they are guaranteed to have `TIDx`s of 0, 1, and 2.
pub struct YaccGrammar {
    /// How many nonterminals does this grammar have?
    nonterms_len: usize,
    /// A mapping from `NTIdx` -> `String`.
    nonterm_names: Vec<String>,
    /// A mapping from `TIdx` -> `Option<String>`. Every user-specified terminal will have a name,
    /// but terminals inserted by cfgrammar (e.g. the EOF terminal) won't.
    term_names: Vec<Option<String>>,
    /// A mapping from `TIdx` -> `Option<Precedence>`
    term_precs: Vec<Option<Precedence>>,
    /// How many terminals does this grammar have?
    terms_len: usize,
    /// The offset of the EOF terminal.
    eof_term_idx: TIdx,
    /// How many productions does this grammar have?
    prods_len: usize,
    /// Which production is the sole production of the start rule?
    start_prod: PIdx,
    /// A list of all productions.
    prods: Vec<Vec<Symbol>>,
    /// A mapping from rules to their productions. Note that 1) the order of rules is identical to
    /// that of `nonterm_names` 2) every rule will have at least 1 production 3) productions
    /// are not necessarily stored sequentially.
    rules_prods: Vec<Vec<PIdx>>,
    /// A mapping from productions to their corresponding rule indexes.
    prods_rules: Vec<NTIdx>,
    /// The precedence of each production.
    prod_precs: Vec<Option<Precedence>>,
    /// The index of the nonterminal added for implicit tokens, if they were specified; otherwise
    /// `None`.
    implicit_nonterm: Option<NTIdx>
}

impl YaccGrammar {
    /// Translate a `GrammarAST` into a `YaccGrammar`. This function is akin to the part a traditional
    /// compiler that takes in an AST and converts it into a binary.
    ///
    /// As we're compiling the `GrammarAST` into a `Grammar` we add a new start rule (which we'll
    /// refer to as "^", though the actual name is a fresh name that is guaranteed to be unique)
    /// that references the user defined start rule.
    pub fn new(yacc_kind: YaccKind, ast: &ast::GrammarAST) -> YaccGrammar {
        // The caller is expected to have called validate before calling this function.
        debug_assert!(ast.validate().is_ok());

        let mut nonterm_names: Vec<String> = Vec::with_capacity(ast.rules.len() + 1);

        // Generate a guaranteed unique start nonterm name. We simply keep making the string longer
        // until we've hit something unique (at the very worst, this will require looping for as
        // many times as there are nonterminals). We use the same technique later for unique end
        // term and whitespace names.
        let mut start_nonterm = START_NONTERM.to_string();
        while ast.rules.get(&start_nonterm).is_some() {
            start_nonterm += START_NONTERM;
        }
        nonterm_names.push(start_nonterm.clone());

        let implicit_nonterm;
        let implicit_start_nonterm;
        match yacc_kind {
            YaccKind::Original => {
                implicit_nonterm = None;
                implicit_start_nonterm = None;
            },
            YaccKind::Eco => {
                if ast.implicit_tokens.is_some() {
                    let mut n1 = IMPLICIT_NONTERM.to_string();
                    while ast.rules.get(&n1).is_some() {
                        n1 += IMPLICIT_NONTERM;
                    }
                    nonterm_names.push(n1.clone());
                    implicit_nonterm = Some(n1);
                    let mut n2 = IMPLICIT_START_NONTERM.to_string();
                    while ast.rules.get(&n2).is_some() {
                        n2 += IMPLICIT_START_NONTERM;
                    }
                    nonterm_names.push(n2.clone());
                    implicit_start_nonterm = Some(n2);
                }
                else {
                    implicit_nonterm = None;
                    implicit_start_nonterm = None;
                }
            }
        };

        for k in ast.rules.keys() {
            nonterm_names.push(k.clone());
        }
        nonterm_names.sort_by(|a, b| a.to_lowercase().cmp(&b.to_lowercase()));
        let mut rules_prods:Vec<Vec<PIdx>> = Vec::with_capacity(nonterm_names.len());
        let mut nonterm_map = HashMap::<String, NTIdx>::new();
        for (i, v) in nonterm_names.iter().enumerate() {
            rules_prods.push(Vec::new());
            nonterm_map.insert(v.clone(), NTIdx(i));
        }

        let mut term_names: Vec<Option<String>> = Vec::with_capacity(ast.tokens.len() + 1);
        let mut term_precs: Vec<Option<Precedence>> = Vec::with_capacity(ast.tokens.len() + 1);
        for k in &ast.tokens {
            term_names.push(Some(k.clone()));
            term_precs.push(ast.precs.get(k).cloned());
        }
        let eof_term_idx = TIdx(term_names.len());
        term_names.push(None);
        term_precs.push(None);
        let mut term_map = HashMap::<String, TIdx>::new();
        for (i, v) in term_names.iter().enumerate() {
            if let Some(n) = v.as_ref() {
               term_map.insert(n.clone(), TIdx(i));
            }
        }

        let mut prods = Vec::new();
        let mut prod_precs: Vec<Option<Precedence>> = Vec::new();
        let mut prods_rules = Vec::new();
        for astrulename in &nonterm_names {
            let rule_idx = nonterm_map[astrulename];
            if astrulename == &start_nonterm {
                // Add the special start rule which has a single production which references a
                // single nonterminal.
                rules_prods.get_mut(usize::from(nonterm_map[astrulename]))
                           .unwrap()
                           .push(prods.len().into());
                let start_prod = match implicit_start_nonterm {
                    None => {
                        // Add ^: S;
                        vec![Symbol::Nonterm(nonterm_map[ast.start.as_ref().unwrap()])]
                    }
                    Some(ref s) => {
                        // An implicit rule has been specified, so the special start rule
                        // needs to reference the intermediate start rule required. Therefore add:
                        //   ^: ^~;
                        vec![Symbol::Nonterm(nonterm_map[s])]
                    }
                };
                prods.push(start_prod);
                prod_precs.push(None);
                prods_rules.push(rule_idx);
                continue;
            }
            else if implicit_start_nonterm.as_ref().map_or(false, |s| s == astrulename) {
                // Add the intermediate start rule (handling implicit tokens at the beginning of
                // the file):
                //   ^~: ~ S;
                rules_prods.get_mut(usize::from(nonterm_map[astrulename]))
                           .unwrap()
                           .push(prods.len().into());
                prods.push(vec![Symbol::Nonterm(nonterm_map[implicit_nonterm.as_ref().unwrap()]),
                                Symbol::Nonterm(nonterm_map[ast.start.as_ref().unwrap()])]);
                prod_precs.push(None);
                prods_rules.push(rule_idx);
                continue;
            }
            else if implicit_nonterm.as_ref().map_or(false, |s| s == astrulename) {
                // Add the implicit rule: ~: "IMPLICIT_TERM1" | ... | "IMPLICIT_TERMN";
                let implicit_prods = rules_prods.get_mut(usize::from(nonterm_map[astrulename])).unwrap();
                // Add a production for each implicit terminal
                for t in ast.implicit_tokens.as_ref().unwrap().iter() {
                    implicit_prods.push(prods.len().into());
                    prods.push(vec![Symbol::Term(term_map[t])]);
                    prod_precs.push(None);
                    prods_rules.push(rule_idx);
                }
                // Add an empty production
                implicit_prods.push(prods.len().into());
                prods.push(vec![]);
                prod_precs.push(None);
                prods_rules.push(rule_idx);
                continue;
            }

            let astrule = &ast.rules[astrulename];
            let mut rule = &mut rules_prods[usize::from(rule_idx)];
            for astprod in &astrule.productions {
                let mut prod = Vec::with_capacity(astprod.symbols.len());
                for astsym in &astprod.symbols {
                    match *astsym {
                        ast::Symbol::Nonterm(ref n) => {
                            prod.push(Symbol::Nonterm(nonterm_map[n]));
                        },
                        ast::Symbol::Term(ref n) => {
                            prod.push(Symbol::Term(term_map[n]));
                            if implicit_nonterm.is_some() {
                                prod.push(Symbol::Nonterm(nonterm_map[&implicit_nonterm.clone().unwrap()]));
                            }
                        }
                    };
                }
                let mut prec = None;
                if let Some(ref n) = astprod.precedence {
                    prec = Some(ast.precs[n]);
                } else {
                    for astsym in astprod.symbols.iter().rev() {
                        if let ast::Symbol::Term(ref n) = *astsym {
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
            nonterms_len:     nonterm_names.len(),
            nonterm_names,
            terms_len:        term_names.len(),
            eof_term_idx:     eof_term_idx,
            term_names,
            term_precs,
            prods_len:        prods.len(),
            start_prod:       rules_prods[usize::from(nonterm_map[&start_nonterm])][0],
            rules_prods,
            prods_rules,
            prods,
            prod_precs,
            implicit_nonterm: implicit_nonterm.map_or(None, |x| Some(nonterm_map[&x]))
        }
    }

    /// Return the index of the end terminal.
    pub fn eof_term_idx(&self) -> TIdx {
        self.eof_term_idx
    }

    /// Return the productions for nonterminal `i` or `None` if it doesn't exist.
    pub fn nonterm_to_prods(&self, i: NTIdx) -> Option<&[PIdx]> {
        self.rules_prods.get(usize::from(i)).map_or(None, |x| Some(x))
    }

    /// Return the name of nonterminal `i` or `None` if it doesn't exist.
    pub fn nonterm_name(&self, i: NTIdx) -> Option<&str> {
        self.nonterm_names.get(usize::from(i)).map_or(None, |x| Some(x))
    }

    /// Return an iterator which produces (in no particular order) all this grammar's valid `NTIdx`s.
    pub fn iter_nonterm_idxs(&self) -> Box<Iterator<Item=NTIdx>> {
        Box::new((0..self.nonterms_len).map(NTIdx))
    }

    /// Get the sequence of symbols for production `i` or `None` if it doesn't exist.
    pub fn prod(&self, i: PIdx) -> Option<&[Symbol]> {
        self.prods.get(usize::from(i)).map_or(None, |x| Some(x))
    }

    /// Return the nonterm index of the production `i` or `None` if it doesn't exist.
    pub fn prod_to_nonterm(&self, i: PIdx) -> NTIdx {
        self.prods_rules[usize::from(i)]
    }

    /// Return the precedence of production `i` or `None` if it doesn't exist.
    pub fn prod_precedence(&self, i: PIdx) -> Option<Option<Precedence>> {
        self.prod_precs.get(usize::from(i)).map_or(None, |x| Some(*x))
    }

    /// Return the name of terminal `i` or `None` if it doesn't exist.
    pub fn term_name(&self, i: TIdx) -> Option<&str> {
        self.term_names.get(usize::from(i)).map_or(None, |x| x.as_ref().map_or(None, |y| Some(&y)))
    }

    /// Return the precedence of terminal `i` or `None` if it doesn't exist.
    pub fn term_precedence(&self, i: TIdx) -> Option<Option<Precedence>> {
        self.term_precs.get(usize::from(i)).map_or(None, |x| Some(*x))
    }

    /// Returns a map from names to `TIdx`s of all tokens that a lexer will need to generate valid
    /// inputs from this grammar.
    pub fn terms_map(&self) -> HashMap<&str, TIdx> {
        let mut m = HashMap::with_capacity(self.terms_len - 1);
        for i in 0..self.terms_len {
            if let Some(n) = self.term_names[i].as_ref() {
                m.insert(&**n, TIdx(i));
            }
        }
        m
    }

    /// Return the production index of the start rule's sole production (for Yacc grammars the
    /// start rule is defined to have precisely one production).
    pub fn start_prod(&self) -> PIdx {
        self.start_prod
    }

    /// Return the `NTIdx` of the implict nonterm if it exists, or `None` otherwise.
    pub fn implicit_nonterm(&self) -> Option<NTIdx> {
        self.implicit_nonterm
    }
}

impl Grammar for YaccGrammar {
    fn prods_len(&self) -> usize {
        self.prods_len
    }

    fn terms_len(&self) -> usize {
        self.terms_len
    }

    fn nonterms_len(&self) -> usize {
        self.nonterms_len
    }

    /// Return the index of the start rule.
    fn start_rule_idx(&self) -> NTIdx {
        self.prod_to_nonterm(self.start_prod)
    }
}

impl YaccGrammar {
    /// Map a nonterminal name to the corresponding rule offset.
    pub fn nonterm_off(&self, n: &str) -> NTIdx {
        NTIdx(self.nonterm_names.iter().position(|x| x == n).unwrap())
    }

    /// Map a terminal name to the corresponding terminal offset.
    pub fn term_off(&self, n: &str) -> TIdx {
        TIdx(self.term_names.iter().position(|x| x.as_ref().map_or(false, |x| x == n)).unwrap())
    }

    /// Map a production number to a rule name.
    pub fn prod_to_term_name(&self, i: PIdx) -> &str {
        &self.nonterm_names[usize::from(self.prod_to_nonterm(i))]
    }
}

#[derive(Debug)]
pub enum YaccGrammarError {
    YaccParserError(YaccParserError),
    GrammarValidationError(GrammarValidationError)
}

impl From<YaccParserError> for YaccGrammarError {
    fn from(err: YaccParserError) -> YaccGrammarError {
        YaccGrammarError::YaccParserError(err)
    }
}

impl From<GrammarValidationError> for YaccGrammarError {
    fn from(err: GrammarValidationError) -> YaccGrammarError {
        YaccGrammarError::GrammarValidationError(err)
    }
}

impl fmt::Display for YaccGrammarError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            YaccGrammarError::YaccParserError(ref e) => e.fmt(f),
            YaccGrammarError::GrammarValidationError(ref e) => e.fmt(f)
        }
    }
}

#[cfg(test)]
mod test {
    use std::collections::HashMap;
    use super::{IMPLICIT_NONTERM, IMPLICIT_START_NONTERM};
    use {NTIdx, PIdx, Symbol, TIdx};
    use yacc::{AssocKind, Precedence, yacc_grm, YaccKind};

    #[test]
    fn test_minimal() {
        let grm = yacc_grm(YaccKind::Original,
                           &"%start R %token T %% R: 'T';".to_string()).unwrap();

        assert_eq!(grm.start_prod, PIdx(0));
        assert_eq!(grm.implicit_nonterm(), None);
        grm.nonterm_off("^");
        grm.nonterm_off("R");
        grm.term_off("T");

        assert_eq!(grm.rules_prods, vec![vec![PIdx(0)], vec![PIdx(1)]]);
        let start_prod = grm.prod(grm.rules_prods[usize::from(grm.nonterm_off("^"))][0]).unwrap();
        assert_eq!(*start_prod, [Symbol::Nonterm(grm.nonterm_off("R"))]);
        let r_prod = grm.prod(grm.rules_prods[usize::from(grm.nonterm_off("R"))][0]).unwrap();
        assert_eq!(*r_prod, [Symbol::Term(grm.term_off("T"))]);
        assert_eq!(grm.prods_rules, vec![NTIdx(0), NTIdx(1)]);

        assert_eq!(grm.terms_map(), [("T", TIdx(0))].iter().cloned().collect::<HashMap<&str, TIdx>>());
        assert_eq!(grm.iter_nonterm_idxs().collect::<Vec<NTIdx>>(), vec![NTIdx(0), NTIdx(1)]);
    }

    #[test]
    fn test_rule_ref() {
        let grm = yacc_grm(YaccKind::Original,
                           &"%start R %token T %% R : S; S: 'T';".to_string()).unwrap();

        grm.nonterm_off("^");
        grm.nonterm_off("R");
        grm.nonterm_off("S");
        grm.term_off("T");
        assert!(grm.term_name(grm.eof_term_idx()).is_none());

        assert_eq!(grm.rules_prods, vec![vec![PIdx(0)], vec![PIdx(1)], vec![PIdx(2)]]);
        let start_prod = grm.prod(grm.rules_prods[usize::from(grm.nonterm_off("^"))][0]).unwrap();
        assert_eq!(*start_prod, [Symbol::Nonterm(grm.nonterm_off("R"))]);
        let r_prod = grm.prod(grm.rules_prods[usize::from(grm.nonterm_off("R"))][0]).unwrap();
        assert_eq!(r_prod.len(), 1);
        assert_eq!(r_prod[0], Symbol::Nonterm(grm.nonterm_off("S")));
        let s_prod = grm.prod(grm.rules_prods[usize::from(grm.nonterm_off("S"))][0]).unwrap();
        assert_eq!(s_prod.len(), 1);
        assert_eq!(s_prod[0], Symbol::Term(grm.term_off("T")));
    }

    #[test]
    fn test_long_prod() {
        let grm = yacc_grm(YaccKind::Original,
                           &"%start R %token T1 T2 %% R : S 'T1' S; S: 'T2';".to_string()).unwrap();

        grm.nonterm_off("^");
        grm.nonterm_off("R");
        grm.nonterm_off("S");
        grm.term_off("T1");
        grm.term_off("T2");

        assert_eq!(grm.rules_prods, vec![vec![PIdx(0)], vec![PIdx(1)], vec![PIdx(2)]]);
        assert_eq!(grm.prods_rules, vec![NTIdx(0), NTIdx(1), NTIdx(2)]);
        let start_prod = grm.prod(grm.rules_prods[usize::from(grm.nonterm_off("^"))][0]).unwrap();
        assert_eq!(*start_prod, [Symbol::Nonterm(grm.nonterm_off("R"))]);
        let r_prod = grm.prod(grm.rules_prods[usize::from(grm.nonterm_off("R"))][0]).unwrap();
        assert_eq!(r_prod.len(), 3);
        assert_eq!(r_prod[0], Symbol::Nonterm(grm.nonterm_off("S")));
        assert_eq!(r_prod[1], Symbol::Term(grm.term_off("T1")));
        assert_eq!(r_prod[2], Symbol::Nonterm(grm.nonterm_off("S")));
        let s_prod = grm.prod(grm.rules_prods[usize::from(grm.nonterm_off("S"))][0]).unwrap();
        assert_eq!(s_prod.len(), 1);
        assert_eq!(s_prod[0], Symbol::Term(grm.term_off("T2")));
    }


    #[test]
    fn test_prods_rules() {
        let grm = yacc_grm(YaccKind::Original, &"
            %start A
            %%
            A: B
             | C;
            B: 'x';
            C: 'y'
             | 'z';
          ".to_string()).unwrap();

        assert_eq!(grm.prods_rules, vec![NTIdx(0), NTIdx(1), NTIdx(1), NTIdx(2), NTIdx(3), NTIdx(3)]);
    }

    #[test]
    fn test_left_right_nonassoc_precs() {
        let grm = yacc_grm(YaccKind::Original, &"
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
          ").unwrap();

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
        let grm = yacc_grm(YaccKind::Original, &"
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
        ").unwrap();
        assert_eq!(grm.prod_precs.len(), 7);
        assert_eq!(grm.prod_precs[0], None);
        assert_eq!(grm.prod_precs[1].unwrap(), Precedence{level: 0, kind: AssocKind::Left});
        assert_eq!(grm.prod_precs[2].unwrap(), Precedence{level: 0, kind: AssocKind::Left});
        assert_eq!(grm.prod_precs[3].unwrap(), Precedence{level: 1, kind: AssocKind::Left});
        assert_eq!(grm.prod_precs[4].unwrap(), Precedence{level: 1, kind: AssocKind::Left});
        assert_eq!(grm.prod_precs[5].unwrap(), Precedence{level: 1, kind: AssocKind::Left});
        assert!(grm.prod_precs[6].is_none());
    }

    #[test]
    fn test_implicit_tokens_rewrite() {
        let grm = yacc_grm(YaccKind::Eco, &"
          %implicit_tokens ws1 ws2
          %start S
          %%
          S: 'a' | T;
          T: 'c' |;
          ").unwrap();

        // Check that the above grammar has been rewritten to:
        //   ^ : ^~;
        //   ^~: ~ S;
        //   ~ : ws1 | ws2 | ;
        //   S : 'a' ~ | T;
        //   T : 'c' ~ | ;

        assert_eq!(grm.prod_precs.len(), 9);

        let itfs_rule_idx = grm.nonterm_off(IMPLICIT_START_NONTERM);
        assert_eq!(grm.rules_prods[usize::from(itfs_rule_idx)].len(), 1);

        let itfs_prod1 = &grm.prods[usize::from(grm.rules_prods[usize::from(itfs_rule_idx)][0])];
        assert_eq!(itfs_prod1.len(), 2);
        assert_eq!(itfs_prod1[0], Symbol::Nonterm(grm.nonterm_off(IMPLICIT_NONTERM)));
        assert_eq!(itfs_prod1[1], Symbol::Nonterm(grm.nonterm_off(&"S")));

        let s_rule_idx = grm.nonterm_off(&"S");
        assert_eq!(grm.rules_prods[usize::from(s_rule_idx)].len(), 2);

        let s_prod1 = &grm.prods[usize::from(grm.rules_prods[usize::from(s_rule_idx)][0])];
        assert_eq!(s_prod1.len(), 2);
        assert_eq!(s_prod1[0], Symbol::Term(grm.term_off("a")));
        assert_eq!(s_prod1[1], Symbol::Nonterm(grm.nonterm_off(IMPLICIT_NONTERM)));

        let s_prod2 = &grm.prods[usize::from(grm.rules_prods[usize::from(s_rule_idx)][1])];
        assert_eq!(s_prod2.len(), 1);
        assert_eq!(s_prod2[0], Symbol::Nonterm(grm.nonterm_off("T")));

        let t_rule_idx = grm.nonterm_off(&"T");
        assert_eq!(grm.rules_prods[usize::from(s_rule_idx)].len(), 2);

        let t_prod1 = &grm.prods[usize::from(grm.rules_prods[usize::from(t_rule_idx)][0])];
        assert_eq!(t_prod1.len(), 2);
        assert_eq!(t_prod1[0], Symbol::Term(grm.term_off("c")));
        assert_eq!(t_prod1[1], Symbol::Nonterm(grm.nonterm_off(IMPLICIT_NONTERM)));

        let t_prod2 = &grm.prods[usize::from(grm.rules_prods[usize::from(t_rule_idx)][1])];
        assert_eq!(t_prod2.len(), 0);

        assert_eq!(Some(grm.nonterm_off(IMPLICIT_NONTERM)), grm.implicit_nonterm());
        let i_rule_idx = grm.nonterm_off(IMPLICIT_NONTERM);
        assert_eq!(grm.rules_prods[usize::from(i_rule_idx)].len(), 3);
        let i_prod1 = &grm.prods[usize::from(grm.rules_prods[usize::from(i_rule_idx)][0])];
        let i_prod2 = &grm.prods[usize::from(grm.rules_prods[usize::from(i_rule_idx)][1])];
        assert_eq!(i_prod1.len(), 1);
        assert_eq!(i_prod2.len(), 1);
        // We don't know what order the implicit nonterminal will contain our tokens in,
        // hence the awkward dance below.
        assert!((i_prod1[0] == Symbol::Term(grm.term_off("ws1"))
                 && (i_prod2[0] == Symbol::Term(grm.term_off("ws2"))))
             || (i_prod1[0] == Symbol::Term(grm.term_off("ws2"))
                 && (i_prod2[0] == Symbol::Term(grm.term_off("ws1")))));
        let i_prod3 = &grm.prods[usize::from(grm.rules_prods[usize::from(i_rule_idx)][2])];
        assert_eq!(i_prod3.len(), 0);
    }
}
