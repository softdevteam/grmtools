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

use std::collections::hash_map::{Entry, HashMap};
use std::hash::{BuildHasherDefault, Hash};

use cfgrammar::{Grammar, PIdx, Symbol, SIdx};
use cfgrammar::yacc::YaccGrammar;
use fnv::FnvHasher;
use num_traits::{AsPrimitive, PrimInt, Unsigned};
use vob::Vob;

use cfgrammar::Firsts;
use cfgrammar::yacc::firsts::YaccFirsts;

/// The type of "context" (also known as "lookaheads")
pub type Ctx = Vob;

#[derive(Clone, Debug, PartialEq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct Itemset<StorageT: Eq + Hash> {
    pub items: HashMap<(PIdx<StorageT>, SIdx<StorageT>), Ctx, BuildHasherDefault<FnvHasher>>
}

impl<StorageT: 'static + Hash + PrimInt + Unsigned> Itemset<StorageT> 
where usize: AsPrimitive<StorageT>
{
    /// Create a blank Itemset.
    pub fn new(_: &YaccGrammar<StorageT>) -> Self {
        Itemset {items: HashMap::with_hasher(BuildHasherDefault::<FnvHasher>::default())}
    }

    /// Add an item `(prod, dot)` with context `ctx` to this itemset. Returns true if this led to
    /// any changes in the itemset.
    pub fn add(&mut self, pidx: PIdx<StorageT>, dot: SIdx<StorageT>, ctx: &Ctx) -> bool {
        let entry = self.items.entry((pidx, dot));
        match entry {
            Entry::Occupied(mut e) => {
                e.get_mut().or(ctx)
            }
            Entry::Vacant(e)       => {
                e.insert(ctx.clone());
                true
            }
        }
    }

    /// Create a new itemset which is a closed version of `self`.
    pub fn close(&self, grm: &YaccGrammar<StorageT>, firsts: &YaccFirsts<StorageT>) -> Self {
        // This function can be seen as a merger of getClosure and getContext from Chen's
        // dissertation.

        let mut new_is = self.clone(); // The new itemset we're building up

        // In a typical description of this algorithm, one would have a todo set which contains
        // pairs (pidx, dot). Unfortunately this is a slow way of doing things. Searching the set
        // for the next item and removing it is slow; and, since we don't know how many potential
        // dots there are in a production, the set is of potentially unbounded size, so we can end
        // up resizing memory. Since this function is the most expensive in the table generation,
        // using a HashSet (which is the "obvious" solution) is slow.
        //
        // However, we can reduce these costs through two observations:
        //   1) The initial todo set is populated with (pidx, dot) pairs that all come from
        //      self.items.keys(). There's no point copying these into a todo list.
        //   2) All subsequent todo items are of the form (prod_off, 0). Since the dot in these
        //      cases is always 0, we don't need to store pairs: simply knowing which prod_off's we
        //      need to look at is sufficient. We can represent these with a fixed-size bitfield.
        // All we need to do is first iterate through the items in 1 and, when it's exhausted,
        // continually iterate over the bitfield from 2 until no new items have been added.

        let mut keys_iter = self.items.keys(); // The initial todo list
        let mut zero_todos = Vob::from_elem(usize::from(grm.prods_len()), false); // Subsequent todos
        let mut new_ctx = Vob::from_elem(usize::from(grm.tokens_len()), false);
        loop {
            let pidx;
            let dot;
            // Find the next todo item or, if there are none, break the loop. First of all we try
            // pumping keys_iter for its next value. If there is none (i.e. we've exhausted that
            // part of the todo set), we iterate over zero_todos.
            match keys_iter.next() {
                Some(&(x, y)) => {
                    pidx = x;
                    dot = y;
                }
                None => {
                    match zero_todos.iter_set_bits(..).next() {
                        Some(i) => {
                            // Since zero_todos.len() == grm.prods_len, the call to as_ is safe.
                            pidx = PIdx(i.as_())
                        },
                        None => break
                    }
                    dot = SIdx(StorageT::zero());
                    zero_todos.set(pidx.into(), false);
                }
            }
            let prod = grm.prod(pidx);
            if dot == grm.prod_len(pidx) { continue; }
            if let Symbol::Rule(s_ridx) = prod[usize::from(dot)] {
                // This if statement is, in essence, a fast version of what's called getContext in
                // Chen's dissertation, folding in getTHeads at the same time. The particular
                // formulation here is based as much on
                // http://binarysculpting.com/2012/02/04/computing-lr1-closure/ as it is any of the
                // several versions of getTHeads in Chen's dissertation. Nevertheless, the mapping
                // between the two different formulations is fairly straight-forward.
                new_ctx.set_all(false);
                let mut nullable = true;
                for sym in prod.iter().skip(usize::from(dot) + 1) {
                    match *sym {
                        Symbol::Token(s_tidx) => {
                            new_ctx.set(usize::from(s_tidx), true);
                            nullable = false;
                            break;
                        },
                        Symbol::Rule(s_ridx) => {
                            new_ctx.or(firsts.firsts(s_ridx));
                            if !firsts.is_epsilon_set(s_ridx) {
                                nullable = false;
                                break;
                            }
                        }
                    }
                }
                if nullable {
                    new_ctx.or(&new_is.items[&(pidx, dot)]);
                }

                for ref_pidx in grm.rule_to_prods(s_ridx).iter() {
                    if new_is.add(*ref_pidx, SIdx(StorageT::zero()), &new_ctx) {
                        zero_todos.set(usize::from(*ref_pidx), true);
                    }
                }
            }
        }
        new_is
    }

    /// Create a new Itemset based on calculating the goto of 'sym' on the current Itemset.
    pub fn goto(&self, grm: &YaccGrammar<StorageT>, sym: &Symbol<StorageT>) -> Self {
        // This is called 'transition' in Chen's dissertation, though note that the definition
        // therein appears to get the dot in the input/output the wrong way around.
        let mut newis = Itemset::new(grm);
        for (&(pidx, dot), ctx) in &self.items {
            let prod = grm.prod(pidx);
            if dot == grm.prod_len(pidx) { continue; }
            if sym == &prod[usize::from(dot)] {
                newis.add(pidx, SIdx(dot.as_storaget() + StorageT::one()), ctx);
            }
        }
        newis
    }
}

#[cfg(test)]
mod test {
    use vob::Vob;
    use super::Itemset;
    use cfgrammar::{Grammar, SIdx, Symbol};
    use cfgrammar::yacc::{YaccGrammar, YaccKind};
    use stategraph::state_exists;

    #[test]
    fn test_dragon_grammar() {
        // From http://binarysculpting.com/2012/02/04/computing-lr1-closure/
        let grm = &YaccGrammar::new(YaccKind::Original, &"
          %start S
          %%
          S: L '=' R | R;
          L: '*' R | 'id';
          R: L;
          ").unwrap();
        let firsts = grm.yacc_firsts();

        let mut is = Itemset::new(&grm);
        let mut la = Vob::from_elem(usize::from(grm.tokens_len()), false);
        la.set(usize::from(grm.eof_token_idx()), true);
        is.add(grm.rule_to_prods(grm.rule_idx("^").unwrap())[0], SIdx(0), &la);
        let cls_is = is.close(&grm, &firsts);
        println!("{:?}", cls_is);
        assert_eq!(cls_is.items.len(), 6);
        state_exists(&grm, &cls_is, "^", 0, SIdx(0), vec!["$"]);
        state_exists(&grm, &cls_is, "S", 0, SIdx(0), vec!["$"]);
        state_exists(&grm, &cls_is, "S", 1, SIdx(0), vec!["$"]);
        state_exists(&grm, &cls_is, "L", 0, SIdx(0), vec!["$", "="]);
        state_exists(&grm, &cls_is, "L", 1, SIdx(0), vec!["$", "="]);
        state_exists(&grm, &cls_is, "R", 0, SIdx(0), vec!["$"]);
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
    fn test_closure1_ecogrm() {
        let grm = eco_grammar();
        let firsts = grm.yacc_firsts();

        let mut is = Itemset::new(&grm);
        let mut la = Vob::from_elem(usize::from(grm.tokens_len()), false);
        la.set(usize::from(grm.eof_token_idx()), true);
        is.add(grm.rule_to_prods(grm.rule_idx("^").unwrap())[0], SIdx(0), &la);
        let mut cls_is = is.close(&grm, &firsts);

        state_exists(&grm, &cls_is, "^", 0, SIdx(0), vec!["$"]);
        state_exists(&grm, &cls_is, "S", 0, SIdx(0), vec!["b", "$"]);
        state_exists(&grm, &cls_is, "S", 1, SIdx(0), vec!["b", "$"]);
        state_exists(&grm, &cls_is, "S", 2, SIdx(0), vec!["b", "$"]);

        is = Itemset::new(&grm);
        is.add(grm.rule_to_prods(grm.rule_idx("F").unwrap())[0], SIdx(0), &la);
        cls_is = is.close(&grm, &firsts);
        state_exists(&grm, &cls_is, "F", 0, SIdx(0), vec!["$"]);
        state_exists(&grm, &cls_is, "C", 0, SIdx(0), vec!["d", "f"]);
        state_exists(&grm, &cls_is, "D", 0, SIdx(0), vec!["a"]);
        state_exists(&grm, &cls_is, "D", 1, SIdx(0), vec!["a"]);
    }

    // GrammarAST from 'LR(k) Analyse fuer Pragmatiker'
    // Z : S
    // S : Sb
    //     bAa
    // A : aSc
    //     a
    //     aSb
    fn grammar3() -> YaccGrammar {
        YaccGrammar::new(YaccKind::Original, &"
          %start S
          %token a b c d
          %%
          S: S 'b' | 'b' A 'a';
          A: 'a' S 'c' | 'a' | 'a' S 'b';
          ").unwrap()
    }

    #[test]
    fn test_closure1_grm3() {
        let grm = grammar3();
        let firsts = grm.yacc_firsts();

        let mut is = Itemset::new(&grm);
        let mut la = Vob::from_elem(usize::from(grm.tokens_len()), false);
        la.set(usize::from(grm.eof_token_idx()), true);
        is.add(grm.rule_to_prods(grm.rule_idx("^").unwrap())[0], SIdx(0), &la);
        let mut cls_is = is.close(&grm, &firsts);

        state_exists(&grm, &cls_is, "^", 0, SIdx(0), vec!["$"]);
        state_exists(&grm, &cls_is, "S", 0, SIdx(0), vec!["b", "$"]);
        state_exists(&grm, &cls_is, "S", 1, SIdx(0), vec!["b", "$"]);

        is = Itemset::new(&grm);
        la = Vob::from_elem(usize::from(grm.tokens_len()), false);
        la.set(usize::from(grm.token_idx("b").unwrap()), true);
        la.set(usize::from(grm.eof_token_idx()), true);
        is.add(grm.rule_to_prods(grm.rule_idx("S").unwrap())[1], SIdx(1), &la);
        cls_is = is.close(&grm, &firsts);
        state_exists(&grm, &cls_is, "A", 0, SIdx(0), vec!["a"]);
        state_exists(&grm, &cls_is, "A", 1, SIdx(0), vec!["a"]);
        state_exists(&grm, &cls_is, "A", 2, SIdx(0), vec!["a"]);

        is = Itemset::new(&grm);
        la = Vob::from_elem(usize::from(grm.tokens_len()), false);
        la.set(usize::from(grm.token_idx("a").unwrap()), true);
        is.add(grm.rule_to_prods(grm.rule_idx("A").unwrap())[0], SIdx(1), &la);
        cls_is = is.close(&grm, &firsts);
        state_exists(&grm, &cls_is, "S", 0, SIdx(0), vec!["b", "c"]);
        state_exists(&grm, &cls_is, "S", 1, SIdx(0), vec!["b", "c"]);
    }

    #[test]
    fn test_goto1() {
        let grm = grammar3();
        let firsts = grm.yacc_firsts();

        let mut is = Itemset::new(&grm);
        let mut la = Vob::from_elem(usize::from(grm.tokens_len()), false);
        la.set(usize::from(grm.eof_token_idx()), true);
        is.add(grm.rule_to_prods(grm.rule_idx("^").unwrap())[0], SIdx(0), &la);
        let cls_is = is.close(&grm, &firsts);

        let goto1 = cls_is.goto(&grm, &Symbol::Rule(grm.rule_idx("S").unwrap()));
        state_exists(&grm, &goto1, "^", 0, SIdx(1), vec!["$"]);
        state_exists(&grm, &goto1, "S", 0, SIdx(1), vec!["$", "b"]);

        // follow 'b' from start set
        let goto2 = cls_is.goto(&grm, &Symbol::Token(grm.token_idx("b").unwrap()));
        state_exists(&grm, &goto2, "S", 1, SIdx(1), vec!["$", "b"]);

        // continue by following 'a' from last goto, after it's been closed
        let goto3 = goto2.close(&grm, &firsts).goto(&grm, &Symbol::Token(grm.token_idx("a").unwrap()));
        state_exists(&grm, &goto3, "A", 1, SIdx(1), vec!["a"]);
        state_exists(&grm, &goto3, "A", 2, SIdx(1), vec!["a"]);
    }
}
