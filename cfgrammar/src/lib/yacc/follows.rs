use std::marker::PhantomData;

use num_traits::{AsPrimitive, PrimInt, Unsigned};
use vob::Vob;

use super::YaccGrammar;
use crate::{RIdx, Symbol, TIdx};

/// `Follows` stores all the Follow sets for a given grammar. For example, given this code and
/// grammar:
/// ```text
///   let grm = YaccGrammar::new(YaccKind::Original(YaccOriginalActionKind::GenericParseTree), "
///       S: A 'b';
///       A: 'a' | ;
///     ").unwrap();
///   let follows = Follows::new(&grm);
/// ```
/// then the following assertions (and only the following assertions) about the Follows set are
/// correct:
/// ```text
///   assert!(follows.is_set(grm.rule_idx("S").unwrap(), grm.eof_token_idx());
///   assert!(follows.is_set(grm.rule_idx("A").unwrap(), grm.token_idx("b").unwrap()));
/// ```
#[derive(Debug)]
pub struct YaccFollows<StorageT> {
    follows: Vec<Vob>,
    phantom: PhantomData<StorageT>,
}

impl<StorageT: 'static + PrimInt + Unsigned> YaccFollows<StorageT>
where
    usize: AsPrimitive<StorageT>,
{
    /// Generates and returns the Follows set for the given grammar.
    pub fn new(grm: &YaccGrammar<StorageT>) -> Self {
        let mut follows = vec![
            Vob::from_elem(usize::from(grm.tokens_len()), false);
            usize::from(grm.rules_len())
        ];
        follows[usize::from(grm.start_rule_idx())].set(usize::from(grm.eof_token_idx()), true);

        let firsts = grm.firsts();
        loop {
            let mut changed = false;
            for pidx in grm.iter_pidxs() {
                let ridx = grm.prod_to_rule(pidx);
                let prod = grm.prod(pidx);
                // Our implementation of the Follows algorithm is simple: we start from the right
                // hand side of a production and work backwards. While epsilon is true, any
                // nonterminals we encounter have the Follow set of the production's rule added to
                // them. As soon as we hit a token or a nonterminal that can't produce the empty
                // string, we set epsilon to false. At that point, we simply add the first set of
                // the following symbol to any nonterminals we encounter.
                let mut epsilon = true;
                for sidx in (0..prod.len()).rev() {
                    let sym = prod[sidx];
                    match sym {
                        Symbol::Token(_) => {
                            epsilon = false;
                        }
                        Symbol::Rule(s_ridx) => {
                            if epsilon {
                                for tidx in grm.iter_tidxs() {
                                    if follows[usize::from(ridx)][usize::from(tidx)]
                                        && follows[usize::from(s_ridx)].set(usize::from(tidx), true)
                                    {
                                        changed = true;
                                    }
                                }
                            }
                            if !firsts.is_epsilon_set(s_ridx) {
                                epsilon = false;
                            }
                            if sidx < prod.len() - 1 {
                                match prod[sidx + 1] {
                                    Symbol::Token(nxt_tidx) => {
                                        if follows[usize::from(s_ridx)]
                                            .set(usize::from(nxt_tidx), true)
                                        {
                                            changed = true;
                                        }
                                    }
                                    Symbol::Rule(nxt_ridx) => {
                                        if follows[usize::from(s_ridx)].or(firsts.firsts(nxt_ridx))
                                        {
                                            changed = true;
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            if !changed {
                return YaccFollows {
                    follows,
                    phantom: PhantomData,
                };
            }
        }
    }

    /// Return the Follows `Vob` for rule `ridx`.
    pub fn follows(&self, ridx: RIdx<StorageT>) -> &Vob {
        &self.follows[usize::from(ridx)]
    }

    /// Returns true if the token `tidx` is in the follow set for rule `ridx`.
    pub fn is_set(&self, ridx: RIdx<StorageT>, tidx: TIdx<StorageT>) -> bool {
        self.follows[usize::from(ridx)][usize::from(tidx)]
    }
}

#[cfg(test)]
mod test {
    use super::{
        super::{YaccGrammar, YaccKind, YaccOriginalActionKind},
        YaccFollows,
    };
    use num_traits::{AsPrimitive, PrimInt, Unsigned};

    fn has<StorageT: 'static + PrimInt + Unsigned>(
        grm: &YaccGrammar<StorageT>,
        follows: &YaccFollows<StorageT>,
        rn: &str,
        should_be: Vec<&str>,
    ) where
        usize: AsPrimitive<StorageT>,
    {
        let ridx = grm.rule_idx(rn).unwrap();
        for tidx in grm.iter_tidxs() {
            let n = if tidx == grm.eof_token_idx() {
                "$"
            } else {
                grm.token_name(tidx).unwrap_or("<no name>")
            };
            if should_be.iter().find(|&x| x == &n).is_none() {
                if follows.is_set(ridx, tidx) {
                    panic!("{} is incorrectly set in {}", n, rn);
                }
            } else if !follows.is_set(ridx, tidx) {
                panic!("{} is not set in {}", n, rn);
            }
        }
    }

    #[test]
    fn test_follow() {
        // Adapted from p2 of https://www.cs.uaf.edu/~cs331/notes/FirstFollow.pdf
        let grm = YaccGrammar::new(
            YaccKind::Original(YaccOriginalActionKind::GenericParseTree),
            &"
                %start E
                %%
                E: T E2 ;
                E2: '+' T E2 | ;
                T: F T2 ;
                T2: '*' F T2 | ;
                F: '(' E ')' | 'ID' ;
          ",
        )
        .unwrap();
        let follows = grm.follows();
        has(&grm, &follows, "E", vec![")", "$"]);
        has(&grm, &follows, "E2", vec![")", "$"]);
        has(&grm, &follows, "T", vec!["+", ")", "$"]);
        has(&grm, &follows, "T2", vec!["+", ")", "$"]);
        has(&grm, &follows, "F", vec!["+", "*", ")", "$"]);
    }

    #[test]
    fn test_follow2() {
        // Adapted from https://www.l2f.inesc-id.pt/~david/w/pt/Top-Down_Parsing/Exercise_5:_Test_2010/07/01
        let grm = YaccGrammar::new(
            YaccKind::Original(YaccOriginalActionKind::GenericParseTree),
            &"
                %start A
                %%
                A : 't' B2 D | 'v' D2 ;
                B : 't' B2 | ;
                B2: 'w' B | 'u' 'w' B ;
                D : 'v' D2 ;
                D2: 'x' B D2 | ;
          ",
        )
        .unwrap();
        let follows = grm.follows();
        has(&grm, &follows, "A", vec!["$"]);
        has(&grm, &follows, "B", vec!["v", "x", "$"]);
        has(&grm, &follows, "B2", vec!["v", "x", "$"]);
        has(&grm, &follows, "D", vec!["$"]);
        has(&grm, &follows, "D2", vec!["$"]);
    }

    #[test]
    fn test_follow3() {
        let grm = YaccGrammar::new(
            YaccKind::Original(YaccOriginalActionKind::GenericParseTree),
            &"
                %start S
                %%
                S: A 'b';
                A: 'b' | ;
          ",
        )
        .unwrap();
        let follows = grm.follows();
        has(&grm, &follows, "S", vec!["$"]);
        has(&grm, &follows, "A", vec!["b"]);
    }

    #[test]
    fn test_follow_corchuelo() {
        let grm = YaccGrammar::new(
            YaccKind::Original(YaccOriginalActionKind::GenericParseTree),
            &"
                %start E
                %%
                E : 'N'
                  | E '+' 'N'
                  | '(' E ')'
                  ;
          ",
        )
        .unwrap();
        let follows = grm.follows();
        has(&grm, &follows, "E", vec!["+", ")", "$"]);
    }
}
