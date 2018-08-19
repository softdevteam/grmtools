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

use std::marker::PhantomData;

use num_traits::{AsPrimitive, PrimInt, Unsigned};
use vob::Vob;

use cfgrammar::{Grammar, NTIdx, Symbol, TIdx};
use cfgrammar::yacc::YaccGrammar;

/// `Firsts` stores all the first sets for a given grammar. For example, given this code and
/// grammar:
/// ```ignore
///   let grm = YaccGrammar::new(YaccKind::Original, "
///     S: A 'b';
///     A: 'a'
///      | ;").unwrap();
///   let firsts = Firsts::new(&grm);
/// ```
/// then the following assertions (and only the following assertions) about the firsts set are
/// correct:
/// ```ignore
///   assert!(firsts.is_set(grm.nonterm_idx("S").unwrap(), grm.term_idx("a").unwrap()));
///   assert!(firsts.is_set(grm.nonterm_idx("S").unwrap(), grm.term_idx("b").unwrap()));
///   assert!(firsts.is_set(grm.nonterm_idx("A").unwrap(), grm.term_idx("a").unwrap()));
///   assert!(firsts.is_epsilon_set(grm.nonterm_idx("A").unwrap()));
/// ```
#[derive(Debug)]
pub struct Firsts<StorageT> {
    prod_firsts: Vec<Vob>,
    prod_epsilons: Vob,
    phantom: PhantomData<StorageT>
}

impl<StorageT: 'static + PrimInt + Unsigned> Firsts<StorageT>
where usize: AsPrimitive<StorageT>
{
    /// Generates and returns the firsts set for the given grammar.
    pub fn new(grm: &YaccGrammar<StorageT>) -> Self {
        let mut prod_firsts = Vec::with_capacity(usize::from(grm.nonterms_len()));
        for _ in grm.iter_ntidxs() {
            prod_firsts.push(Vob::from_elem(usize::from(grm.terms_len()), false));
        }
        let mut firsts = Firsts {
            prod_firsts,
            prod_epsilons: Vob::from_elem(usize::from(grm.nonterms_len()), false),
            phantom      : PhantomData
        };

        // Loop looking for changes to the firsts set, until we reach a fixed point. In essence, we
        // look at each rule E, and see if any of the nonterminals at the start of its productions
        // have new elements in since we last looked. If they do, we'll have to do another round.
        loop {
            let mut changed = false;
            for rul_i in grm.iter_ntidxs() {
                // For each rule E
                for prod_i in grm.nonterm_to_prods(rul_i).iter() {
                    // ...and each production A
                    let prod = grm.prod(*prod_i);
                    if prod.is_empty() {
                        // if it's an empty production, ensure this nonterminal's epsilon bit is
                        // set.
                        if !firsts.is_epsilon_set(rul_i) {
                            firsts.prod_epsilons.set(usize::from(rul_i), true);
                            changed = true;
                        }
                        continue;
                    }
                    for (sym_i, sym) in prod.iter().enumerate() {
                        match *sym {
                            Symbol::Term(term_i) => {
                                // if symbol is a Term, add to FIRSTS
                                if !firsts.set(rul_i, term_i) {
                                    changed = true;
                                }
                                break;
                            },
                            Symbol::Nonterm(nonterm_i) => {
                                // if we're dealing with another Nonterm, union its FIRSTs
                                // together with the current nonterminals FIRSTs. Note this is
                                // (intentionally) a no-op if the two terminals are one and the
                                // same.
                                for tidx in grm.iter_tidxs() {
                                    if firsts.is_set(nonterm_i, tidx) && !firsts.set(rul_i, tidx) {
                                        changed = true;
                                    }
                                }

                                // If the epsilon bit in the nonterminal being referenced is set,
                                // and if its the last symbol in the production, then add epsilon
                                // to FIRSTs.
                                if firsts.is_epsilon_set(nonterm_i) && sym_i == prod.len() - 1 {
                                    // Only add epsilon if the symbol is the last in the production
                                    if !firsts.prod_epsilons[usize::from(rul_i)] {
                                        firsts.prod_epsilons.set(usize::from(rul_i), true);
                                        changed = true;
                                    }
                                }

                                // If FIRST(X) of production R : X Y2 Y3 doesn't contain epsilon,
                                // then don't try and calculate the FIRSTS of Y2 or Y3 (i.e. stop
                                // now).
                                if !firsts.is_epsilon_set(nonterm_i) {
                                    break;
                                }
                            },
                        }
                    }
                }
            }
            if !changed {
                return firsts;
            }
        }
    }

    /// Returns true if the terminal `tidx` is in the first set for nonterminal `nidx` is set.
    pub fn is_set(&self, nidx: NTIdx<StorageT>, tidx: TIdx<StorageT>) -> bool {
        self.prod_firsts[usize::from(nidx)][usize::from(tidx)]
    }

    /// Get all the firsts for production `ntidx`.
    pub fn prod_firsts(&self, ntidx: NTIdx<StorageT>) -> &Vob {
        &self.prod_firsts[usize::from(ntidx)]
    }

    /// Returns true if the nonterminal `ntidx` has epsilon in its first set.
    pub fn is_epsilon_set(&self, ntidx: NTIdx<StorageT>) -> bool {
        self.prod_epsilons[usize::from(ntidx)]
    }

    /// Ensures that the firsts bit for terminal `tidx` nonterminal `nidx` is set. Returns true if
    /// it was already set, or false otherwise.
    pub fn set(&mut self, ntidx: NTIdx<StorageT>, tidx: TIdx<StorageT>) -> bool {
        let prod = &mut self.prod_firsts[usize::from(ntidx)];
        if prod[usize::from(tidx)] {
            true
        }
        else {
            prod.set(usize::from(tidx), true);
            false
        }
    }
}


#[cfg(test)]
mod test {
    use cfgrammar::Grammar;
    use cfgrammar::yacc::{YaccGrammar, YaccKind};
    use num_traits::{AsPrimitive, PrimInt, Unsigned};

    use super::Firsts;

    fn has<StorageT: 'static + PrimInt + Unsigned>
          (grm: &YaccGrammar<StorageT>, firsts: &Firsts<StorageT>, rn: &str, should_be: Vec<&str>)
     where usize: AsPrimitive<StorageT>
    {
        let nt_i = grm.nonterm_idx(rn).unwrap();
        for tidx in grm.iter_tidxs() {
            let n = match grm.term_name(tidx) {
                Some(n) => n,
                None => &"<no name>"
            };
            match should_be.iter().position(|&x| x == n) {
                Some(_) => {
                    if !firsts.is_set(nt_i, tidx) {
                        panic!("{} is not set in {}", n, rn);
                    }
                }
                None    => {
                    if firsts.is_set(nt_i, tidx) {
                        panic!("{} is incorrectly set in {}", n, rn);
                    }
                }
            }
        }
        if should_be.iter().position(|x| x == &"").is_some() {
            assert!(firsts.is_epsilon_set(nt_i));
        }
    }

    #[test]
    fn test_first(){
        let grm = YaccGrammar::new(YaccKind::Original, &"
          %start C
          %token c d
          %%
          C: 'c';
          D: 'd';
          E: D | C;
          F: E;
          ").unwrap();
        let firsts = Firsts::new(&grm);
        has(&grm, &firsts, "^", vec!["c"]);
        has(&grm, &firsts, "D", vec!["d"]);
        has(&grm, &firsts, "E", vec!["d", "c"]);
        has(&grm, &firsts, "F", vec!["d", "c"]);
    }

    #[test]
    fn test_first_no_subsequent_nonterminals() {
        let grm = YaccGrammar::new(YaccKind::Original, &"
          %start C
          %token c d
          %%
          C: 'c';
          D: 'd';
          E: D C;
          ").unwrap();
        let firsts = Firsts::new(&grm);
        has(&grm, &firsts, "E", vec!["d"]);
    }

    #[test]
    fn test_first_epsilon() {
        let grm = YaccGrammar::new(YaccKind::Original, &"
          %start A
          %token a b c
          %%
          A: B 'a';
          B: 'b' | ;
          C: 'c' | ;
          D: C;
          ").unwrap();
        let firsts = Firsts::new(&grm);
        has(&grm, &firsts, "A", vec!["b", "a"]);
        has(&grm, &firsts, "C", vec!["c", ""]);
        has(&grm, &firsts, "D", vec!["c", ""]);
    }

    #[test]
    fn test_last_epsilon() {
        let grm = YaccGrammar::new(YaccKind::Original, &"
          %start A
          %token b c
          %%
          A: B C;
          B: 'b' | ;
          C: B 'c' B;
          ").unwrap();
        let firsts = Firsts::new(&grm);
        has(&grm, &firsts, "A", vec!["b", "c"]);
        has(&grm, &firsts, "B", vec!["b", ""]);
        has(&grm, &firsts, "C", vec!["b", "c"]);
    }

    #[test]
    fn test_first_no_multiples() {
        let grm = YaccGrammar::new(YaccKind::Original, &"
          %start A
          %token b c
          %%
          A: B 'b';
          B: 'b' | ;
          ").unwrap();
        let firsts = Firsts::new(&grm);
        has(&grm, &firsts, "A", vec!["b"]);
    }

    fn eco_grammar() -> YaccGrammar {
        YaccGrammar::new(YaccKind::Original, &"
          %start S
          %token a b c d f
          %%
          S: S 'b' | 'b' A 'a' | 'a';
          A: 'a' S 'c' | 'a' | 'a' S 'b';
          B: A S;
          C: D A;
          D: 'd' | ;
          F: C D 'f';
          ").unwrap()
    }

    #[test]
    fn test_first_from_eco() {
        let grm = eco_grammar();
        let firsts = Firsts::new(&grm);
        has(&grm, &firsts, "S", vec!["a", "b"]);
        has(&grm, &firsts, "A", vec!["a"]);
        has(&grm, &firsts, "B", vec!["a"]);
        has(&grm, &firsts, "D", vec!["d", ""]);
        has(&grm, &firsts, "C", vec!["d", "a"]);
        has(&grm, &firsts, "F", vec!["d", "a"]);
    }

    #[test]
    fn test_first_from_eco_bug() {
        let grm = YaccGrammar::new(YaccKind::Original, &"
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
          ").unwrap();
        let firsts = Firsts::new(&grm);
        has(&grm, &firsts, "E", vec!["a"]);
        has(&grm, &firsts, "T", vec!["a"]);
        has(&grm, &firsts, "P", vec!["a"]);
        has(&grm, &firsts, "C", vec!["c", ""]);
        has(&grm, &firsts, "D", vec!["f", "d", ""]);
        has(&grm, &firsts, "G", vec!["c", "d", "f", ""]);
    }
}
