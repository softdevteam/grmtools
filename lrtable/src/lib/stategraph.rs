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

use std::collections::hash_map::HashMap;
use std::hash::Hash;

use cfgrammar::{Symbol, TIdx};
use cfgrammar::yacc::YaccGrammar;
use num_traits::{PrimInt, Unsigned};

use StIdx;
use itemset::Itemset;

#[derive(Debug)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct StateGraph<StorageT: Eq + Hash> {
    /// A vector of `(core_states, closed_states)` tuples.
    states: Vec<(Itemset<StorageT>, Itemset<StorageT>)>,
    /// For each state in `states`, edges is a hashmap from symbols to state offsets.
    edges: Vec<HashMap<Symbol<StorageT>, StIdx>>
}

impl<StorageT: Hash + PrimInt + Unsigned> StateGraph<StorageT> {
    pub(crate) fn new(states: Vec<(Itemset<StorageT>, Itemset<StorageT>)>,
                      edges: Vec<HashMap<Symbol<StorageT>, StIdx>>)
                   -> Self
    {
        StateGraph{states, edges}
    }

    /// Return the itemset for closed state `st_idx`. Panics if `st_idx` doesn't exist.
    pub fn closed_state(&self, st_idx: StIdx) -> &Itemset<StorageT> {
        &self.states[usize::from(st_idx)].1
    }

    /// Return an iterator over all closed states in this `StateGraph`.
    pub fn iter_closed_states<'a>(&'a self) -> Box<Iterator<Item=&'a Itemset<StorageT>> + 'a> {
        Box::new(self.states.iter().map(|x| &x.1))
    }

    /// Return the itemset for core state `st_idx` or `None` if it doesn't exist.
    pub fn core_state(&self, st_idx: StIdx) -> &Itemset<StorageT> {
        &self.states[usize::from(st_idx)].0
    }

    /// Return an iterator over all core states in this `StateGraph`.
    pub fn iter_core_states<'a>(&'a self) -> Box<Iterator<Item=&'a Itemset<StorageT>> + 'a> {
        Box::new(self.states.iter().map(|x| &x.0))
    }

    /// How many states does this `StateGraph` contain? NB: By definition the `StateGraph` contains
    /// the same number of core and closed states.
    pub fn all_states_len(&self) -> u32 {
        debug_assert!(self.states.len() <= u32::max_value() as usize);
        self.states.len() as u32
    }

    /// Return the state pointed to by `sym` from `st_idx` or `None` otherwise.
    pub fn edge(&self, st_idx: StIdx, sym: Symbol<StorageT>) -> Option<StIdx> {
        self.edges.get(usize::from(st_idx))
                  .and_then(|x| x.get(&sym))
                  .cloned()
    }

    /// Return the edges for state `st_idx`. Panics if `st_idx` doesn't exist.
    pub fn edges(&self, st_idx: StIdx) -> &HashMap<Symbol<StorageT>, StIdx> {
        &self.edges[usize::from(st_idx)]
    }

    /// How many edges does this `StateGraph` contain?
    pub fn all_edges_len(&self) -> usize {
        self.edges.iter().fold(0, |a, x| a + x.len())
    }

    fn pp(&self, grm: &YaccGrammar<StorageT>, core_states: bool) -> String {
        fn num_digits(i: u32) -> usize {
            // In an ideal world, we'd do ((i as f64).log10() as usize) + 1, but we then hit
            // floating point rounding errors (e.g. 1000.0.log10() == 2.999999999ish, not
            // 3). So we do the lazy thing, convert the number to a string and do things that way.
            i.to_string().len()
        }

        fn fmt_sym<StorageT: PrimInt + Unsigned>(grm: &YaccGrammar<StorageT>, sym: Symbol<StorageT>) -> String {
            match sym {
                Symbol::Nonterm(ntidx) => grm.nonterm_name(ntidx).to_string(),
                Symbol::Term(tidx) => format!("'{}'", grm.term_name(tidx).unwrap_or(""))
            }
        }

        let mut o = String::new();
        for (st_idx, &(ref core_st, ref closed_st)) in self.states.iter().enumerate() {
            if st_idx > 0 {
                o.push_str(&"\n");
            }
            {
                let padding = num_digits(self.all_states_len()) - num_digits(st_idx as u32);
                o.push_str(&format!("{}:{}", st_idx, " ".repeat(padding)));
            }

            let st = if core_states {
                core_st
            } else {
                closed_st
            };
            for (i, (&(p_idx, s_idx), ref ctx)) in st.items.iter().enumerate() {
                let padding = if i == 0 {
                    0
                } else {
                    o.push_str("\n "); // Extra space to compensate for ":" printed above
                    num_digits(self.all_states_len())
                };
                o.push_str(&format!("{} [{} ->",
                                    " ".repeat(padding),
                                    grm.nonterm_name(grm.prod_to_nonterm(p_idx))));
                for (is_idx, is_sym) in grm.prod(p_idx).iter().enumerate() {
                    if is_idx == usize::from(s_idx) {
                        o.push_str(" .");
                    }
                    o.push_str(&format!(" {}", fmt_sym(&grm, *is_sym)));
                }
                if usize::from(s_idx) == grm.prod(p_idx).len() {
                    o.push_str(" .");
                }
                o.push_str(", {");
                let mut seen_b = false;
                for b_idx in ctx.iter_set_bits(..) {
                    if seen_b {
                        o.push_str(", ");
                    } else {
                        seen_b = true;
                    }
                    let tidx = TIdx::from(b_idx);
                    if tidx == grm.eof_term_idx() {
                        o.push_str("'$'");
                    } else {
                        o.push_str(&format!("'{}'", grm.term_name(tidx).unwrap()));
                    }
                }
                o.push_str("}]");
            }
            for (esym, e_st_idx) in self.edges(StIdx::from(st_idx)).iter() {
                o.push_str(&format!("\n{}{} -> {}",
                                   " ".repeat(num_digits(self.all_states_len()) + 2),
                                   fmt_sym(&grm, *esym),
                                   usize::from(*e_st_idx)));
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
use cfgrammar::{Grammar};

#[cfg(test)]
pub fn state_exists<StorageT: Hash + PrimInt + Unsigned>
                   (grm: &YaccGrammar<StorageT>,
                    is: &Itemset<StorageT>,
                    nt: &str,
                    prod_off: usize,
                    dot: usize, la: Vec<&str>)
{
    let ab_prod_off = grm.nonterm_to_prods(grm.nonterm_idx(nt).unwrap())[prod_off];
    let ctx = &is.items[&(ab_prod_off, dot.into())];
    for i in 0..grm.terms_len() as usize {
        let bit = ctx[i];
        let mut found = false;
        for t in la.iter() {
            let off = if t == &"$" {
                    TIdx::from(grm.eof_term_idx())
                } else {
                    grm.term_idx(t).unwrap()
                };
            if off == i.into() {
                if !bit {
                    panic!("bit for terminal {}, dot {} is not set in production {} of {} when it should be",
                           t, dot, prod_off, nt);
                }
                found = true;
                break;
            }
        }
        if !found && bit {
            panic!("bit for terminal {}, dot {} is set in production {} of {} when it shouldn't be",
                   grm.term_name(i.into()).unwrap(), dot, prod_off, nt);
        }
    }
}

#[cfg(test)]
mod test {
    use cfgrammar::{Symbol};
    use cfgrammar::yacc::{YaccGrammar, YaccKind};
    use StIdx;
    use pager::pager_stategraph;

    #[test]
    fn test_statetable_core() {
        // Taken from p13 of https://link.springer.com/article/10.1007/s00236-010-0115-6
        let grm = YaccGrammar::new(YaccKind::Original, &"
            %start A
            %%
            A: 'OPEN_BRACKET' A 'CLOSE_BRACKET'
             | 'a'
             | 'b';
          ").unwrap();
        let sg = pager_stategraph(&grm);
        assert_eq!(sg.all_states_len(), 7);
        assert_eq!(sg.states.iter().fold(0, |a, x| a + x.0.items.len()), 7);
        assert_eq!(sg.all_edges_len(), 9);

        // This follows the (not particularly logical) ordering of state numbers in the paper.
        let s0 = StIdx::from(0 as u32);
        sg.edge(s0, Symbol::Nonterm(grm.nonterm_idx("A").unwrap())).unwrap(); // s1
        let s2 = sg.edge(s0, Symbol::Term(grm.term_idx("a").unwrap())).unwrap();
        let s3 = sg.edge(s0, Symbol::Term(grm.term_idx("b").unwrap())).unwrap();
        let s5 = sg.edge(s0, Symbol::Term(grm.term_idx("OPEN_BRACKET").unwrap())).unwrap();
        assert_eq!(s2, sg.edge(s5, Symbol::Term(grm.term_idx("a").unwrap())).unwrap());
        assert_eq!(s3, sg.edge(s5, Symbol::Term(grm.term_idx("b").unwrap())).unwrap());
        assert_eq!(s5, sg.edge(s5, Symbol::Term(grm.term_idx("OPEN_BRACKET").unwrap())).unwrap());
        let s4 = sg.edge(s5, Symbol::Nonterm(grm.nonterm_idx("A").unwrap())).unwrap();
        sg.edge(s4, Symbol::Term(grm.term_idx("CLOSE_BRACKET").unwrap())).unwrap(); // s6
    }
}
