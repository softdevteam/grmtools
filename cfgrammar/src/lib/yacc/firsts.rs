use std::marker::PhantomData;

use num_traits::{AsPrimitive, PrimInt, Unsigned};
use vob::Vob;

use super::YaccGrammar;
use crate::{RIdx, Symbol, TIdx};

/// `Firsts` stores all the first sets for a given grammar. For example, given this code and
/// grammar:
/// ```text
///   let grm = YaccGrammar::new(YaccKind::Original(YaccOriginalActionKind::GenericParseTree), "
///     S: A 'b';
///     A: 'a'
///      | ;").unwrap();
///   let firsts = Firsts::new(&grm);
/// ```
/// then the following assertions (and only the following assertions) about the firsts set are
/// correct:
/// ```text
///   assert!(firsts.is_set(grm.rule_idx("S").unwrap(), grm.token_idx("a").unwrap()));
///   assert!(firsts.is_set(grm.rule_idx("S").unwrap(), grm.token_idx("b").unwrap()));
///   assert!(firsts.is_set(grm.rule_idx("A").unwrap(), grm.token_idx("a").unwrap()));
///   assert!(firsts.is_epsilon_set(grm.rule_idx("A").unwrap()));
/// ```
#[derive(Debug)]
pub struct YaccFirsts<StorageT> {
    firsts: Vec<Vob>,
    epsilons: Vob,
    phantom: PhantomData<StorageT>,
}

impl<StorageT: 'static + PrimInt + Unsigned> YaccFirsts<StorageT>
where
    usize: AsPrimitive<StorageT>,
{
    /// Generates and returns the firsts set for the given grammar.
    pub fn new(grm: &YaccGrammar<StorageT>) -> Self {
        let mut firsts = YaccFirsts {
            firsts: vec![
                Vob::from_elem(usize::from(grm.tokens_len()), false);
                usize::from(grm.rules_len())
            ],
            epsilons: Vob::from_elem(usize::from(grm.rules_len()), false),
            phantom: PhantomData,
        };

        // Loop looking for changes to the firsts set, until we reach a fixed point. In essence, we
        // look at each rule E, and see if any of the rules at the start of its productions
        // have new elements in since we last looked. If they do, we'll have to do another round.
        loop {
            let mut changed = false;
            for ridx in grm.iter_rules() {
                // For each rule E
                for &pidx in grm.rule_to_prods(ridx).iter() {
                    // ...and each production A
                    let prod = grm.prod(pidx);
                    if prod.is_empty() {
                        // if it's an empty production, ensure this rule's epsilon bit is
                        // set.
                        if !firsts.is_epsilon_set(ridx) {
                            firsts.epsilons.set(usize::from(ridx), true);
                            changed = true;
                        }
                        continue;
                    }
                    for (sidx, sym) in prod.iter().enumerate() {
                        match *sym {
                            Symbol::Token(s_tidx) => {
                                // if symbol is a token, add to FIRSTS
                                if !firsts.set(ridx, s_tidx) {
                                    changed = true;
                                }
                                break;
                            }
                            Symbol::Rule(s_ridx) => {
                                // if we're dealing with another rule, union its FIRSTs
                                // together with the current rules FIRSTs. Note this is
                                // (intentionally) a no-op if the two tokens are one and the
                                // same.
                                for tidx in grm.iter_tidxs() {
                                    if firsts.is_set(s_ridx, tidx) && !firsts.set(ridx, tidx) {
                                        changed = true;
                                    }
                                }

                                // If the epsilon bit in the rule being referenced is set,
                                // and if its the last symbol in the production, then add epsilon
                                // to FIRSTs.
                                if firsts.is_epsilon_set(s_ridx) && sidx == prod.len() - 1 {
                                    // Only add epsilon if the symbol is the last in the production
                                    if !firsts.epsilons[usize::from(ridx)] {
                                        firsts.epsilons.set(usize::from(ridx), true);
                                        changed = true;
                                    }
                                }

                                // If FIRST(X) of production R : X Y2 Y3 doesn't contain epsilon,
                                // then don't try and calculate the FIRSTS of Y2 or Y3 (i.e. stop
                                // now).
                                if !firsts.is_epsilon_set(s_ridx) {
                                    break;
                                }
                            }
                        }
                    }
                }
            }
            if !changed {
                return firsts;
            }
        }
    }

    /// Return all the firsts for rule `ridx`.
    pub fn firsts(&self, ridx: RIdx<StorageT>) -> &Vob {
        &self.firsts[usize::from(ridx)]
    }

    /// Returns true if the token `tidx` is in the first set for rule `ridx`.
    pub fn is_set(&self, ridx: RIdx<StorageT>, tidx: TIdx<StorageT>) -> bool {
        self.firsts[usize::from(ridx)][usize::from(tidx)]
    }

    /// Returns true if the rule `ridx` has epsilon in its first set.
    pub fn is_epsilon_set(&self, ridx: RIdx<StorageT>) -> bool {
        self.epsilons[usize::from(ridx)]
    }

    /// Ensures that the firsts bit for token `tidx` rule `ridx` is set. Returns true if
    /// it was already set, or false otherwise.
    pub fn set(&mut self, ridx: RIdx<StorageT>, tidx: TIdx<StorageT>) -> bool {
        let r = &mut self.firsts[usize::from(ridx)];
        if r[usize::from(tidx)] {
            true
        } else {
            r.set(usize::from(tidx), true);
            false
        }
    }
}

#[cfg(test)]
mod test {
    use super::{
        super::{YaccGrammar, YaccKind, YaccOriginalActionKind},
        YaccFirsts,
    };
    use num_traits::{AsPrimitive, PrimInt, Unsigned};

    fn has<StorageT: 'static + PrimInt + Unsigned>(
        grm: &YaccGrammar<StorageT>,
        firsts: &YaccFirsts<StorageT>,
        rn: &str,
        should_be: Vec<&str>,
    ) where
        usize: AsPrimitive<StorageT>,
    {
        let ridx = grm.rule_idx(rn).unwrap();
        for tidx in grm.iter_tidxs() {
            let n = match grm.token_name(tidx) {
                Some(n) => n,
                None => &"<no name>",
            };
            match should_be.iter().position(|&x| x == n) {
                Some(_) => {
                    if !firsts.is_set(ridx, tidx) {
                        panic!("{} is not set in {}", n, rn);
                    }
                }
                None => {
                    if firsts.is_set(ridx, tidx) {
                        panic!("{} is incorrectly set in {}", n, rn);
                    }
                }
            }
        }
        if should_be.iter().any(|x| x == &"") {
            assert!(firsts.is_epsilon_set(ridx));
        }
    }

    #[test]
    fn test_first() {
        let grm = YaccGrammar::new(
            YaccKind::Original(YaccOriginalActionKind::GenericParseTree),
            &"
          %start C
          %token c d
          %%
          C: 'c';
          D: 'd';
          E: D | C;
          F: E;
          ",
        )
        .unwrap();
        let firsts = grm.firsts();
        has(&grm, &firsts, "^", vec!["c"]);
        has(&grm, &firsts, "D", vec!["d"]);
        has(&grm, &firsts, "E", vec!["d", "c"]);
        has(&grm, &firsts, "F", vec!["d", "c"]);
    }

    #[test]
    fn test_first_no_subsequent_rules() {
        let grm = YaccGrammar::new(
            YaccKind::Original(YaccOriginalActionKind::GenericParseTree),
            &"
          %start C
          %token c d
          %%
          C: 'c';
          D: 'd';
          E: D C;
          ",
        )
        .unwrap();
        let firsts = grm.firsts();
        has(&grm, &firsts, "E", vec!["d"]);
    }

    #[test]
    fn test_first_epsilon() {
        let grm = YaccGrammar::new(
            YaccKind::Original(YaccOriginalActionKind::GenericParseTree),
            &"
          %start A
          %token a b c
          %%
          A: B 'a';
          B: 'b' | ;
          C: 'c' | ;
          D: C;
          ",
        )
        .unwrap();
        let firsts = grm.firsts();
        has(&grm, &firsts, "A", vec!["b", "a"]);
        has(&grm, &firsts, "C", vec!["c", ""]);
        has(&grm, &firsts, "D", vec!["c", ""]);
    }

    #[test]
    fn test_last_epsilon() {
        let grm = YaccGrammar::new(
            YaccKind::Original(YaccOriginalActionKind::GenericParseTree),
            &"
          %start A
          %token b c
          %%
          A: B C;
          B: 'b' | ;
          C: B 'c' B;
          ",
        )
        .unwrap();
        let firsts = grm.firsts();
        has(&grm, &firsts, "A", vec!["b", "c"]);
        has(&grm, &firsts, "B", vec!["b", ""]);
        has(&grm, &firsts, "C", vec!["b", "c"]);
    }

    #[test]
    fn test_first_no_multiples() {
        let grm = YaccGrammar::new(
            YaccKind::Original(YaccOriginalActionKind::GenericParseTree),
            &"
          %start A
          %token b c
          %%
          A: B 'b';
          B: 'b' | ;
          ",
        )
        .unwrap();
        let firsts = grm.firsts();
        has(&grm, &firsts, "A", vec!["b"]);
    }

    fn eco_grammar() -> YaccGrammar {
        YaccGrammar::new(
            YaccKind::Original(YaccOriginalActionKind::GenericParseTree),
            &"
          %start S
          %token a b c d f
          %%
          S: S 'b' | 'b' A 'a' | 'a';
          A: 'a' S 'c' | 'a' | 'a' S 'b';
          B: A S;
          C: D A;
          D: 'd' | ;
          F: C D 'f';
          ",
        )
        .unwrap()
    }

    #[test]
    fn test_first_from_eco() {
        let grm = eco_grammar();
        let firsts = grm.firsts();
        has(&grm, &firsts, "S", vec!["a", "b"]);
        has(&grm, &firsts, "A", vec!["a"]);
        has(&grm, &firsts, "B", vec!["a"]);
        has(&grm, &firsts, "D", vec!["d", ""]);
        has(&grm, &firsts, "C", vec!["d", "a"]);
        has(&grm, &firsts, "F", vec!["d", "a"]);
    }

    #[test]
    fn test_first_from_eco_bug() {
        let grm = YaccGrammar::new(
            YaccKind::Original(YaccOriginalActionKind::GenericParseTree),
            &"
          %start E
          %token a b c d e f
          %%
          E : T | E 'b' T;
          T : P | T 'e' P;
          P : 'a';
          C: C 'c' | ;
          D: D 'd' | F;
          F: 'f' | ;
          G: C D;
          ",
        )
        .unwrap();
        let firsts = grm.firsts();
        has(&grm, &firsts, "E", vec!["a"]);
        has(&grm, &firsts, "T", vec!["a"]);
        has(&grm, &firsts, "P", vec!["a"]);
        has(&grm, &firsts, "C", vec!["c", ""]);
        has(&grm, &firsts, "D", vec!["f", "d", ""]);
        has(&grm, &firsts, "G", vec!["c", "d", "f", ""]);
    }
}
