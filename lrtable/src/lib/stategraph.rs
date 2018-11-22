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

use std::{collections::hash_map::HashMap, hash::Hash};

use cfgrammar::{yacc::YaccGrammar, Symbol, TIdx};
use num_traits::{AsPrimitive, PrimInt, Unsigned};
use try_from::TryFrom;

use itemset::Itemset;
use StIdx;
use StIdxStorageT;

#[derive(Debug)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct StateGraph<StorageT: Eq + Hash> {
    /// A vector of `(core_states, closed_states)` tuples.
    states: Vec<(Itemset<StorageT>, Itemset<StorageT>)>,
    /// For each state in `states`, edges is a hashmap from symbols to state offsets.
    edges: Vec<HashMap<Symbol<StorageT>, StIdx>>
}

impl<StorageT: 'static + Hash + PrimInt + Unsigned> StateGraph<StorageT>
where
    usize: AsPrimitive<StorageT>
{
    pub(crate) fn new(
        states: Vec<(Itemset<StorageT>, Itemset<StorageT>)>,
        edges: Vec<HashMap<Symbol<StorageT>, StIdx>>
    ) -> Self {
        // states.len() needs to fit into StIdxStorageT; however we don't need to worry about
        // edges.len() (which merely needs to fit in a usize)
        assert!(StIdxStorageT::try_from(states.len()).is_ok());
        StateGraph { states, edges }
    }

    /// Return an iterator which produces (in order from `0..self.rules_len()`) all this
    /// grammar's valid `RIdx`s.
    pub fn iter_stidxs(&self) -> Box<dyn Iterator<Item = StIdx>> {
        // We can use as safely, because we know that we're only generating integers from
        // 0..self.states.len() which we've already checked fits within StIdxStorageT.
        Box::new((0..self.states.len()).map(|x| StIdx(x as StIdxStorageT)))
    }

    /// Return the itemset for closed state `stidx`. Panics if `stidx` doesn't exist.
    pub fn closed_state(&self, stidx: StIdx) -> &Itemset<StorageT> {
        &self.states[usize::from(stidx)].1
    }

    /// Return an iterator over all closed states in this `StateGraph`.
    pub fn iter_closed_states<'a>(&'a self) -> Box<Iterator<Item = &'a Itemset<StorageT>> + 'a> {
        Box::new(self.states.iter().map(|x| &x.1))
    }

    /// Return the itemset for core state `stidx` or `None` if it doesn't exist.
    pub fn core_state(&self, stidx: StIdx) -> &Itemset<StorageT> {
        &self.states[usize::from(stidx)].0
    }

    /// Return an iterator over all core states in this `StateGraph`.
    pub fn iter_core_states<'a>(&'a self) -> Box<Iterator<Item = &'a Itemset<StorageT>> + 'a> {
        Box::new(self.states.iter().map(|x| &x.0))
    }

    /// How many states does this `StateGraph` contain? NB: By definition the `StateGraph` contains
    /// the same number of core and closed states.
    pub fn all_states_len(&self) -> StIdx {
        // We checked in the constructor that self.states.len() can fit into StIdxStorageT
        StIdx::from(self.states.len() as StIdxStorageT)
    }

    /// Return the state pointed to by `sym` from `stidx` or `None` otherwise.
    pub fn edge(&self, stidx: StIdx, sym: Symbol<StorageT>) -> Option<StIdx> {
        self.edges
            .get(usize::from(stidx))
            .and_then(|x| x.get(&sym))
            .cloned()
    }

    /// Return the edges for state `stidx`. Panics if `stidx` doesn't exist.
    pub fn edges(&self, stidx: StIdx) -> &HashMap<Symbol<StorageT>, StIdx> {
        &self.edges[usize::from(stidx)]
    }

    /// How many edges does this `StateGraph` contain?
    pub fn all_edges_len(&self) -> usize {
        self.edges.iter().fold(0, |a, x| a + x.len())
    }

    /// Pretty print this stategraph as a `String`. If `core_states` is set to true, only the core
    /// states are pretty printed; if set to false, all states (including non-core states) are
    /// pretty printed.
    pub fn pp(&self, grm: &YaccGrammar<StorageT>, core_states: bool) -> String {
        fn num_digits(i: StIdx) -> usize {
            if usize::from(i) == 0 {
                1
            } else {
                ((usize::from(i) as f64).log10() as usize) + 1
            }
        }

        fn fmt_sym<StorageT: 'static + PrimInt + Unsigned>(
            grm: &YaccGrammar<StorageT>,
            sym: Symbol<StorageT>
        ) -> String
        where
            usize: AsPrimitive<StorageT>
        {
            match sym {
                Symbol::Rule(ridx) => grm.rule_name(ridx).to_string(),
                Symbol::Token(tidx) => format!("'{}'", grm.token_name(tidx).unwrap_or(""))
            }
        }

        let mut o = String::new();
        for (stidx, &(ref core_st, ref closed_st)) in self.iter_stidxs().zip(self.states.iter()) {
            if StIdxStorageT::from(stidx) > 0 {
                o.push_str(&"\n");
            }
            {
                let padding = num_digits(self.all_states_len()) - num_digits(stidx);
                o.push_str(&format!(
                    "{}:{}",
                    StIdxStorageT::from(stidx),
                    " ".repeat(padding)
                ));
            }

            let st = if core_states { core_st } else { closed_st };
            for (i, (&(pidx, sidx), ref ctx)) in st.items.iter().enumerate() {
                let padding = if i == 0 {
                    0
                } else {
                    o.push_str("\n "); // Extra space to compensate for ":" printed above
                    num_digits(self.all_states_len())
                };
                o.push_str(&format!(
                    "{} [{} ->",
                    " ".repeat(padding),
                    grm.rule_name(grm.prod_to_rule(pidx))
                ));
                for (i_sidx, i_ssym) in grm.prod(pidx).iter().enumerate() {
                    if i_sidx == usize::from(sidx) {
                        o.push_str(" .");
                    }
                    o.push_str(&format!(" {}", fmt_sym(&grm, *i_ssym)));
                }
                if usize::from(sidx) == grm.prod(pidx).len() {
                    o.push_str(" .");
                }
                o.push_str(", {");
                let mut seen_b = false;
                for bidx in ctx.iter_set_bits(..) {
                    if seen_b {
                        o.push_str(", ");
                    } else {
                        seen_b = true;
                    }
                    // Since ctx is exactly tokens_len bits long, the call to as_ is safe.
                    let tidx = TIdx(bidx.as_());
                    if tidx == grm.eof_token_idx() {
                        o.push_str("'$'");
                    } else {
                        o.push_str(&format!("'{}'", grm.token_name(tidx).unwrap()));
                    }
                }
                o.push_str("}]");
            }
            for (esym, e_stidx) in self.edges(stidx).iter() {
                o.push_str(&format!(
                    "\n{}{} -> {}",
                    " ".repeat(num_digits(self.all_states_len()) + 2),
                    fmt_sym(&grm, *esym),
                    usize::from(*e_stidx)
                ));
            }
        }
        o
    }

    /// Return a pretty printed version of the core states, and all edges.
    pub fn pp_core_states(&self, grm: &YaccGrammar<StorageT>) -> String {
        self.pp(grm, true)
    }

    /// Return a pretty printed version of the closed states, and all edges.
    pub fn pp_closed_states(&self, grm: &YaccGrammar<StorageT>) -> String {
        self.pp(grm, false)
    }
}

#[cfg(test)]
use cfgrammar::SIdx;

#[cfg(test)]
pub fn state_exists<StorageT: 'static + Hash + PrimInt + Unsigned>(
    grm: &YaccGrammar<StorageT>,
    is: &Itemset<StorageT>,
    nt: &str,
    prod_off: usize,
    dot: SIdx<StorageT>,
    la: Vec<&str>
) where
    usize: AsPrimitive<StorageT>
{
    let ab_prod_off = grm.rule_to_prods(grm.rule_idx(nt).unwrap())[prod_off];
    let ctx = &is.items[&(ab_prod_off, dot)];
    for tidx in grm.iter_tidxs() {
        let bit = ctx[usize::from(tidx)];
        let mut found = false;
        for t in la.iter() {
            let off = if t == &"$" {
                grm.eof_token_idx()
            } else {
                grm.token_idx(t).unwrap()
            };
            if off == tidx {
                if !bit {
                    panic!("bit for token {}, dot {} is not set in production {} of {} when it should be",
                           t, usize::from(dot), prod_off, nt);
                }
                found = true;
                break;
            }
        }
        if !found && bit {
            panic!(
                "bit for token {}, dot {} is set in production {} of {} when it shouldn't be",
                grm.token_name(tidx).unwrap(),
                usize::from(dot),
                prod_off,
                nt
            );
        }
    }
}

#[cfg(test)]
mod test {
    use cfgrammar::{
        yacc::{YaccGrammar, YaccKind},
        Symbol
    };
    use pager::pager_stategraph;
    use StIdx;

    #[test]
    #[rustfmt::skip]
    fn test_statetable_core() {
        // Taken from p13 of https://link.springer.com/article/10.1007/s00236-010-0115-6
        let grm = YaccGrammar::new(
            YaccKind::Original,
            &"
            %start A
            %%
            A: 'OPEN_BRACKET' A 'CLOSE_BRACKET'
             | 'a'
             | 'b';
          "
        ).unwrap();
        let sg = pager_stategraph(&grm);
        assert_eq!(sg.all_states_len(), StIdx(7));
        assert_eq!(sg.states.iter().fold(0, |a, x| a + x.0.items.len()), 7);
        assert_eq!(sg.all_edges_len(), 9);

        // This follows the (not particularly logical) ordering of state numbers in the paper.
        let s0 = StIdx(0);
        sg.edge(s0, Symbol::Rule(grm.rule_idx("A").unwrap())).unwrap(); // s1
        let s2 = sg.edge(s0, Symbol::Token(grm.token_idx("a").unwrap())).unwrap();
        let s3 = sg.edge(s0, Symbol::Token(grm.token_idx("b").unwrap())).unwrap();
        let s5 = sg.edge(s0, Symbol::Token(grm.token_idx("OPEN_BRACKET").unwrap())).unwrap();
        assert_eq!(s2, sg.edge(s5, Symbol::Token(grm.token_idx("a").unwrap())).unwrap());
        assert_eq!(s3, sg.edge(s5, Symbol::Token(grm.token_idx("b").unwrap())).unwrap());
        assert_eq!(s5, sg.edge(s5, Symbol::Token(grm.token_idx("OPEN_BRACKET").unwrap())).unwrap());
        let s4 = sg.edge(s5, Symbol::Rule(grm.rule_idx("A").unwrap())).unwrap();
        sg.edge(s4, Symbol::Token(grm.token_idx("CLOSE_BRACKET").unwrap())).unwrap(); // s6
    }
}
