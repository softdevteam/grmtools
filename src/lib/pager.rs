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

use std::collections::HashSet;
use std::collections::hash_map::HashMap;

extern crate bit_vec;
use self::bit_vec::BitVec;

use StIdx;
use firsts::Firsts;
use grammar::{Grammar, Symbol, SIdx};
use itemset::Itemset;
use stategraph::StateGraph;

// This file creates stategraphs from grammars. Unfortunately there is no perfect guide to how to
// do this that I know of -- certainly not one that talks about sensible ways to arrange data and
// low-level optimisations. That said, the general algorithms that form the basis of what's used in
// this file can be found in:
//
//   A Practical General Method for Constructing LR(k) Parsers
//     David Pager, Acta Informatica 7, 249--268, 1977
//
// However Pager's paper is dense, and doesn't name sub-parts of the algorithm. We mostly reference
// the (still incomplete, but less incomplete) version of the algorithm found in:
//
//   Measuring and extending LR(1) parser generation
//     Xin Chen, PhD thesis, University of Hawaii, 2009

impl Itemset {
    /// Return true if `other` is weakly compatible with `self`.
    fn weakly_compatible(&self, other: &Itemset) -> bool {
        // The weakly compatible check is one of the three core parts of Pager's algorithm
        // (along with merging and change propagation). In essence, there are three conditions
        // which, if satisfied, guarantee that `other` is weakly compatible with `self`
        // (p255 of Pager's paper, and p50 of Chen's dissertation).
        //
        // Since neither Pager nor Chen talk about data-structures, they don't provide an algorithm
        // for sensibly checking these three conditions. The approach in this function is 1) try
        // and fail at the earliest point that we notice that the two itemsets can't be weakly
        // compatible 2) perform the checks of all three conditions in one go.

        // The two itemsets must have the same number of core configurations. Since our itemsets
        // only store core configurations, two itemsets with different numbers of items can't
        // possibly be weakly compatible.
        let len = self.items.len();
        if len != other.items.len() {
            return false;
        }

        // Check that each itemset has the same core configuration.
        for &(prod_i, dot) in self.items.keys() {
            if other.items.get(&(prod_i, dot)).is_none() {
                return false;
            }
        }

        // If there's only one core configuration to deal with -- which happens surprisingly often
        // -- then the for loop below will always return true, so we save ourselves allocating
        // memory and bail out early.
        if len == 1 {
            return true;
        }

        // Pager's conditions rely on itemsets being ordered. However, ours are stored as hashmaps:
        // iterating over self.items and other.items will not generally give the same order of
        // configurations.
        //
        // The most practical thing we can do is to convert one of the itemsets's keys into a list
        // and use that as a stable ordering mechanism. This uses more hash lookups than we might
        // like, but we're helped by the fact that most itemsets are smallish in number.
        let keys: Vec<_> = self.items.keys().collect();
        for (i, i_key) in keys.iter().enumerate().take(len - 1) {
            for j_key in keys.iter().take(len).skip(i + 1) {
                // Condition 1 in the Pager paper
                if !(bitvec_intersect(&self.items[*i_key], &other.items[*j_key])
                    || bitvec_intersect(&self.items[*j_key], &other.items[*i_key])) {
                    continue;
                }
                // Conditions 2 and 3 in the Pager paper
                if bitvec_intersect(&self.items[*i_key], &self.items[*j_key])
                   || bitvec_intersect(&other.items[*i_key], &other.items[*j_key]) {
                    continue;
                }
                return false;
            }
        }

        true
    }

    /// Merge `other` into `self`, returning `true` if this led to any changes. If `other` is not
    /// weakly compatible with `self`, this function's effects and return value are undefined.
    fn weakly_merge(&mut self, other: &Itemset) -> bool {
        let mut changed = false;
        for (&(prod_i, dot), ctx) in &mut self.items {
            if ctx.union(&other.items[&(prod_i, dot)]) {
                changed = true;
            }
        }
        changed
    }
}

/// Returns true if two identically sized bitvecs intersect.
fn bitvec_intersect(v1: &BitVec, v2: &BitVec) -> bool {
    // Iterating over integer sized blocks allows us to do this operation very quickly. Note that
    // the BitVec implementation guarantees that the last block's unused bits will be zeroed out.
    for (b1, b2) in v1.blocks().zip(v2.blocks()) {
        if b1 & b2 != 0 { return true; }
    }
    false
}

/// Create a `StateGraph` from 'grm'.
pub fn pager_stategraph(grm: &Grammar) -> StateGraph {
    // This function can be seen as a modified version of items() from Chen's dissertation.

    let firsts                                 = Firsts::new(grm);
    // closed_states and core_states are both equally sized vectors of states. Core states are
    // smaller, and used for the weakly compatible checks, but we ultimately need to return
    // closed states. Closed states which are None are those which require processing; thus
    // closed_states also implicitly serves as a todo list.
    let mut closed_states                      = Vec::new();
    let mut core_states                        = Vec::new();
    let mut edges: Vec<HashMap<Symbol, StIdx>> = Vec::new();

    let mut state0 = Itemset::new(grm);
    let mut ctx = BitVec::from_elem(grm.terms_len, false);
    ctx.set(grm.end_term.into(), true);
    state0.add(grm.start_prod, SIdx::from(0), &ctx);
    closed_states.push(None);
    core_states.push(state0);
    edges.push(HashMap::new());

    // We maintain two lists of which nonterms and terms we've seen; when processing a given
    // state there's no point processing a nonterm or term more than once.
    let mut seen_nonterms = BitVec::from_elem(grm.nonterms_len, false);
    let mut seen_terms = BitVec::from_elem(grm.terms_len, false);
    // new_states is used to separate out iterating over states vs. mutating it
    let mut new_states = Vec::new();
    // cnd_[nonterm|term]_weaklies represent which states are possible weakly compatible
    // matches for a given symbol.
    let mut cnd_nonterm_weaklies: Vec<Vec<StIdx>> = Vec::with_capacity(grm.nonterms_len);
    let mut cnd_term_weaklies: Vec<Vec<StIdx>> = Vec::with_capacity(grm.terms_len);
    for _ in 0..grm.terms_len { cnd_term_weaklies.push(Vec::new()); }
    for _ in 0..grm.nonterms_len { cnd_nonterm_weaklies.push(Vec::new()); }

    let mut todo = 1; // How many None values are there in closed_states?
    let mut todo_off = 0; // Offset in closed states to start searching for the next todo.
    while todo > 0 {
        debug_assert_eq!(closed_states.len(), core_states.len());
        // state_i is the next item to process. We don't want to continually search for the
        // next None from the beginning, so we remember where we last saw a None (todo_off) and
        // search from that point onwards, wrapping as necessary. Since processing a state x
        // disproportionately causes state x + 1 to require processing, this prevents the
        // search from becoming horribly non-linear.
        let state_i = match closed_states.iter().skip(todo_off).position(|x| x.is_none()) {
            Some(i) => todo_off + i,
            None    => closed_states.iter().position(|x| x.is_none()).unwrap()
        };
        todo_off = state_i + 1;
        todo -= 1;

        {
            closed_states[state_i] = Some(core_states[state_i].close(grm, &firsts));
            let cl_state = &closed_states[state_i].as_ref().unwrap();
            seen_nonterms.clear();
            seen_terms.clear();
            for &(prod_i, dot) in cl_state.items.keys() {
                let prod = grm.prod(prod_i).unwrap();
                if dot == prod.len().into() { continue; }
                let sym = prod[usize::from(dot)];
                match sym {
                    Symbol::Nonterminal(nonterm_i) => {
                        if seen_nonterms[usize::from(nonterm_i)] {
                            continue;
                        }
                        seen_nonterms.set(usize::from(nonterm_i), true);
                    },
                    Symbol::Terminal(term_i) => {
                        if seen_terms[usize::from(term_i)] {
                            continue;
                        }
                        seen_terms.set(usize::from(term_i), true);
                    }
                }
                let nstate = cl_state.goto(grm, &sym);
                new_states.push((sym, nstate));
            }
        }

        'a: for (sym, nstate) in new_states.drain(..) {
            let mut m = None;
            {
                // Try and compatible match for this state.
                let cnd_states = match sym {
                    Symbol::Nonterminal(nonterm_i) => &cnd_nonterm_weaklies[usize::from(nonterm_i)],
                    Symbol::Terminal(term_i) => &cnd_term_weaklies[usize::from(term_i)]
                };
                // First of all see if any of the candidate states are exactly the same as the
                // new state, in which case we only need to add an edge to the candidate
                // state. This isn't just an optimisation (though it does avoid the expense
                // of change propagation), but has a correctness aspect: there's no guarantee
                // that the weakly compatible check is reflexive (i.e. a state may not be
                // weakly compatible with itself).
                for cnd in cnd_states.iter().map(|x| *x) {
                    if core_states[usize::from(cnd)] == nstate {
                        edges[state_i].insert(sym, cnd);
                        continue 'a;
                    }
                }
                // No candidate states were equal to the new state, so we need to look for a
                // candidate state which is weakly compatible.
                for cnd in cnd_states.iter().cloned() {
                    if core_states[usize::from(cnd)].weakly_compatible(&nstate) {
                        m = Some(cnd);
                        break;
                    }
                }
            }
            match m {
                Some(k) => {
                    // A weakly compatible match has been found.
                    edges[state_i].insert(sym, k);
                    if core_states[usize::from(k)].weakly_merge(&nstate) {
                        // We only do the simplest change propagation, forcing possibly
                        // affected sets to be entirely reprocessed (which will recursively
                        // force propagation too). Even though this does unnecessary
                        // computation, it is still pretty fast.
                        //
                        // Note also that edges[k] will be completely regenerated, overwriting
                        // all existing entries and possibly adding new ones. We thus don't
                        // need to clear it manually.
                        if closed_states[usize::from(k)].is_some() {
                            closed_states[usize::from(k)] = None;
                            todo += 1;
                        }
                    }
                },
                None    => {
                    match sym {
                        Symbol::Nonterminal(nonterm_i) =>
                            cnd_nonterm_weaklies[usize::from(nonterm_i)].push(StIdx(core_states.len())),
                        Symbol::Terminal(term_i) =>
                            cnd_term_weaklies[usize::from(term_i)].push(StIdx(core_states.len())),
                    }
                    edges[state_i].insert(sym, StIdx(core_states.len()));
                    edges.push(HashMap::new());
                    closed_states.push(None);
                    core_states.push(nstate);
                    todo += 1;
                }
            }
        }
    }

    // Although the Pager paper doesn't talk about it, the algorithm above can create
    // unreachable states due to the non-determinism inherent in working with hashsets. Indeed,
    // this can even happen with the example from Pager's paper (on perhaps 1 out of
    // 100 runs, 24 or 25 states will be created instead of 23). We thus need to weed out
    // unreachable states and update edges accordingly.
    let (closed_states, edges) = gc(closed_states.drain(..)
                                                             .map(|x| x.unwrap())
                                                             .collect(),
                                                edges);

    StateGraph {
        states: closed_states,
        edges:  edges
    }
}

/// Garbage collect `states` and `edges`. Returns a new pair with unused states and their
/// corresponding edges removed.
fn gc(mut states: Vec<Itemset>, mut edges: Vec<HashMap<Symbol, StIdx>>)
      -> (Vec<Itemset>, Vec<HashMap<Symbol, StIdx>>) {
    // First of all, do a simple pass over all states. All state indexes reachable from the
    // start state will be inserted into the 'seen' set.
    let mut todo = HashSet::new();
    todo.insert(StIdx(0));
    let mut seen = HashSet::new();
    while !todo.is_empty() {
        // XXX This is the clumsy way we're forced to do what we'd prefer to be:
        //     "let &(prod_i, dot) = todo.pop()"
        let state_i = *todo.iter().next().unwrap();
        todo.remove(&state_i);
        seen.insert(state_i);

        todo.extend(edges[usize::from(state_i)].values().filter(|x| !seen.contains(x)));
    }

    if states.len() == seen.len() {
        // Nothing to garbage collect.
        return (states, edges);
    }

    // Imagine we started with 3 states and their edges:
    //   states: [0, 1, 2]
    //   edges : [[_ => 2]]
    //
    // At this point, 'seen' will be the set {0, 2}. What we need to do is to create a new list
    // of states that doesn't have state 1 in it. That will cause state 2 to become to state 1,
    // meaning that we need to adjust edges so that the pointer to state 2 is updated to state
    // 1. In other words we want to achieve this output:
    //   states: [0, 2]
    //   edges : [_ => 1]
    //
    // The way we do this is to first iterate over all states, working out what the mapping
    // from seen states to their new offsets is.
    let mut gc_states = Vec::with_capacity(seen.len());
    let mut offsets   = Vec::with_capacity(states.len());
    let mut offset    = 0;
    for (state_i, state) in states.drain(..).enumerate().map(|(x, y)| (StIdx(x), y)) {
        offsets.push(StIdx(usize::from(state_i) - offset));
        if !seen.contains(&state_i) {
            offset += 1;
            continue;
        }
        gc_states.push(state);
    }

    // At this point the offsets list will be [0, 1, 1]. We now create new edges where each
    // offset is corrected by looking it up in the offsets list.
    let mut gc_edges = Vec::with_capacity(seen.len());
    for (st_edge_i, st_edges) in edges.drain(..).enumerate().map(|(x, y)| (StIdx(x), y)) {
        if !seen.contains(&st_edge_i) {
            continue;
        }
        gc_edges.push(st_edges.iter().map(|(&k, &v)| (k, offsets[usize::from(v)])).collect());
    }

    (gc_states, gc_edges)
}

#[cfg(test)]
mod test {
    extern crate bit_vec;
    use self::bit_vec::BitVec;

    use super::bitvec_intersect;
    use grammar::{Grammar, Symbol};
    use pager::pager_stategraph;
    use stategraph::state_exists;
    use yacc_parser::parse_yacc;

    #[test]
    fn test_bitvec_intersect() {
        let mut b1 = BitVec::from_elem(8, false);
        let mut b2 = BitVec::from_elem(8, false);
        assert!(!bitvec_intersect(&b1, &b2));
        // Check that partial blocks (i.e. when only part of a word is used in the bitvec for
        // storage) maintain the expected guarantees.
        b1.push(false);
        b2.push(false);
        assert!(!bitvec_intersect(&b1, &b2));
        b1.push(true);
        b2.push(true);
        assert!(bitvec_intersect(&b1, &b2));

        b1 = BitVec::from_elem(64, false);
        b2 = BitVec::from_elem(64, false);
        b1.push(true);
        b2.push(true);
        for _ in 0..63 {
            b1.push(false);
            b2.push(false);
        }
        assert!(bitvec_intersect(&b1, &b2));
    }

    // GrammarAST from 'LR(k) Analyse fuer Pragmatiker'
    // Z : S
    // S : Sb
    //     bAa
    // A : aSc
    //     a
    //     aSb
    fn grammar3() -> Grammar {
        Grammar::new(&parse_yacc(&"
          %start S
          %token a b c d
          %%
          S: S 'b' | 'b' A 'a';
          A: 'a' S 'c' | 'a' | 'a' S 'b';
          ".to_string()).unwrap())
    }

    #[test]
    fn test_stategraph() {
        let grm = grammar3();
        let sg = pager_stategraph(&grm);

        assert_eq!(sg.states.len(), 10);
        assert_eq!(sg.edges.iter().fold(0, |a, e| a + e.len()), 10);

        assert_eq!(sg.states[0].items.len(), 3);
        state_exists(&grm, &sg.states[0], "^", 0, 0, vec!["$"]);
        state_exists(&grm, &sg.states[0], "S", 0, 0, vec!["$", "b"]);
        state_exists(&grm, &sg.states[0], "S", 1, 0, vec!["$", "b"]);

        let s1 = sg.edges[0][&Symbol::Nonterminal(grm.nonterminal_off("S"))];
        assert_eq!(sg.states[usize::from(s1)].items.len(), 2);
        state_exists(&grm, &sg.states[usize::from(s1)], "^", 0, 1, vec!["$"]);
        state_exists(&grm, &sg.states[usize::from(s1)], "S", 0, 1, vec!["$", "b"]);

        let s2 = sg.edges[usize::from(s1)][&Symbol::Terminal(grm.terminal_off("b"))];
        assert_eq!(sg.states[usize::from(s2)].items.len(), 1);
        state_exists(&grm, &sg.states[usize::from(s2)], "S", 0, 2, vec!["$", "b"]);

        let s3 = sg.edges[0][&Symbol::Terminal(grm.terminal_off("b"))];
        assert_eq!(sg.states[usize::from(s3)].items.len(), 4);
        state_exists(&grm, &sg.states[usize::from(s3)], "S", 1, 1, vec!["$", "b", "c"]);
        state_exists(&grm, &sg.states[usize::from(s3)], "A", 0, 0, vec!["a"]);
        state_exists(&grm, &sg.states[usize::from(s3)], "A", 1, 0, vec!["a"]);
        state_exists(&grm, &sg.states[usize::from(s3)], "A", 2, 0, vec!["a"]);

        let s4 = sg.edges[usize::from(s3)][&Symbol::Nonterminal(grm.nonterminal_off("A"))];
        assert_eq!(sg.states[usize::from(s4)].items.len(), 1);
        state_exists(&grm, &sg.states[usize::from(s4)], "S", 1, 2, vec!["$", "b", "c"]);

        let s5 = sg.edges[usize::from(s4)][&Symbol::Terminal(grm.terminal_off("a"))];
        assert_eq!(sg.states[usize::from(s5)].items.len(), 1);
        state_exists(&grm, &sg.states[usize::from(s5)], "S", 1, 3, vec!["$", "b", "c"]);

        let s6 = sg.edges[usize::from(s3)][&Symbol::Terminal(grm.terminal_off("a"))];
        // result from merging 10 into 3
        assert_eq!(s3, sg.edges[usize::from(s6)][&Symbol::Terminal(grm.terminal_off("b"))]);
        assert_eq!(sg.states[usize::from(s6)].items.len(), 5);
        state_exists(&grm, &sg.states[usize::from(s6)], "A", 0, 1, vec!["a"]);
        state_exists(&grm, &sg.states[usize::from(s6)], "A", 1, 1, vec!["a"]);
        state_exists(&grm, &sg.states[usize::from(s6)], "A", 2, 1, vec!["a"]);
        state_exists(&grm, &sg.states[usize::from(s6)], "S", 0, 0, vec!["b", "c"]);
        state_exists(&grm, &sg.states[usize::from(s6)], "S", 1, 0, vec!["b", "c"]);

        let s7 = sg.edges[usize::from(s6)][&Symbol::Nonterminal(grm.nonterminal_off("S"))];
        assert_eq!(sg.states[usize::from(s7)].items.len(), 3);
        state_exists(&grm, &sg.states[usize::from(s7)], "A", 0, 2, vec!["a"]);
        state_exists(&grm, &sg.states[usize::from(s7)], "A", 2, 2, vec!["a"]);
        state_exists(&grm, &sg.states[usize::from(s7)], "S", 0, 1, vec!["b", "c"]);

        let s8 = sg.edges[usize::from(s7)][&Symbol::Terminal(grm.terminal_off("c"))];
        assert_eq!(sg.states[usize::from(s8)].items.len(), 1);
        state_exists(&grm, &sg.states[usize::from(s8)], "A", 0, 3, vec!["a"]);

        let s9 = sg.edges[usize::from(s7)][&Symbol::Terminal(grm.terminal_off("b"))];
        assert_eq!(sg.states[usize::from(s9)].items.len(), 2);
        state_exists(&grm, &sg.states[usize::from(s9)], "A", 2, 3, vec!["a"]);
        state_exists(&grm, &sg.states[usize::from(s9)], "S", 0, 2, vec!["b", "c"]);
    }

    // Pager grammar
    fn grammar_pager() -> Grammar {
        Grammar::new(&parse_yacc(&"
            %start X
            %%
             X : 'a' Y 'd' | 'a' Z 'c' | 'a' T | 'b' Y 'e' | 'b' Z 'd' | 'b' T;
             Y : 't' W | 'u' X;
             Z : 't' 'u';
             T : 'u' X 'a';
             W : 'u' V;
             V : ;
          ".to_string()).unwrap())
    }

    fn test_pager_graph(grm: &Grammar) {
        let sg = pager_stategraph(&grm);

        assert_eq!(sg.states.len(), 23);
        assert_eq!(sg.edges.iter().fold(0, |a, e| a + e.len()), 27);

        // State 0
        assert_eq!(sg.states[0].items.len(), 7);
        state_exists(&grm, &sg.states[0], "^", 0, 0, vec!["$"]);
        state_exists(&grm, &sg.states[0], "X", 0, 0, vec!["$"]);
        state_exists(&grm, &sg.states[0], "X", 1, 0, vec!["$"]);
        state_exists(&grm, &sg.states[0], "X", 2, 0, vec!["$"]);
        state_exists(&grm, &sg.states[0], "X", 3, 0, vec!["$"]);
        state_exists(&grm, &sg.states[0], "X", 4, 0, vec!["$"]);
        state_exists(&grm, &sg.states[0], "X", 5, 0, vec!["$"]);

        let s1 = sg.edges[0][&Symbol::Terminal(grm.terminal_off("a"))];
        assert_eq!(sg.states[usize::from(s1)].items.len(), 7);
        state_exists(&grm, &sg.states[usize::from(s1)], "X", 0, 1, vec!["a", "d", "e", "$"]);
        state_exists(&grm, &sg.states[usize::from(s1)], "X", 1, 1, vec!["a", "d", "e", "$"]);
        state_exists(&grm, &sg.states[usize::from(s1)], "X", 2, 1, vec!["a", "d", "e", "$"]);
        state_exists(&grm, &sg.states[usize::from(s1)], "Y", 0, 0, vec!["d"]);
        state_exists(&grm, &sg.states[usize::from(s1)], "Y", 1, 0, vec!["d"]);
        state_exists(&grm, &sg.states[usize::from(s1)], "Z", 0, 0, vec!["c"]);
        state_exists(&grm, &sg.states[usize::from(s1)], "T", 0, 0, vec!["a", "d", "e", "$"]);

        let s7 = sg.edges[0][&Symbol::Terminal(grm.terminal_off("b"))];
        assert_eq!(sg.states[usize::from(s7)].items.len(), 7);
        state_exists(&grm, &sg.states[usize::from(s7)], "X", 3, 1, vec!["a", "d", "e", "$"]);
        state_exists(&grm, &sg.states[usize::from(s7)], "X", 4, 1, vec!["a", "d", "e", "$"]);
        state_exists(&grm, &sg.states[usize::from(s7)], "X", 5, 1, vec!["a", "d", "e", "$"]);
        state_exists(&grm, &sg.states[usize::from(s1)], "Y", 0, 0, vec!["d"]);
        state_exists(&grm, &sg.states[usize::from(s1)], "Y", 1, 0, vec!["d"]);
        state_exists(&grm, &sg.states[usize::from(s1)], "Z", 0, 0, vec!["c"]);
        state_exists(&grm, &sg.states[usize::from(s1)], "T", 0, 0, vec!["a", "d", "e", "$"]);

        let s4 = sg.edges[usize::from(s1)][&Symbol::Terminal(grm.terminal_off("u"))];
        assert_eq!(sg.states[usize::from(s4)].items.len(), 8);
        assert_eq!(s4, sg.edges[usize::from(s7)][&Symbol::Terminal(grm.terminal_off("u"))]);
        state_exists(&grm, &sg.states[usize::from(s4)], "Y", 1, 1, vec!["d", "e"]);
        state_exists(&grm, &sg.states[usize::from(s4)], "T", 0, 1, vec!["a", "d", "e", "$"]);
        state_exists(&grm, &sg.states[usize::from(s4)], "X", 0, 0, vec!["a", "d", "e"]);
        state_exists(&grm, &sg.states[usize::from(s4)], "X", 1, 0, vec!["a", "d", "e"]);
        state_exists(&grm, &sg.states[usize::from(s4)], "X", 2, 0, vec!["a", "d", "e"]);
        state_exists(&grm, &sg.states[usize::from(s4)], "X", 3, 0, vec!["a", "d", "e"]);
        state_exists(&grm, &sg.states[usize::from(s4)], "X", 4, 0, vec!["a", "d", "e"]);
        state_exists(&grm, &sg.states[usize::from(s4)], "X", 5, 0, vec!["a", "d", "e"]);

        assert_eq!(s1, sg.edges[usize::from(s4)][&Symbol::Terminal(grm.terminal_off("a"))]);
        assert_eq!(s7, sg.edges[usize::from(s4)][&Symbol::Terminal(grm.terminal_off("b"))]);

        let s2 = sg.edges[usize::from(s1)][&Symbol::Terminal(grm.terminal_off("t"))];
        assert_eq!(sg.states[usize::from(s2)].items.len(), 3);
        state_exists(&grm, &sg.states[usize::from(s2)], "Y", 0, 1, vec!["d"]);
        state_exists(&grm, &sg.states[usize::from(s2)], "Z", 0, 1, vec!["c"]);
        state_exists(&grm, &sg.states[usize::from(s2)], "W", 0, 0, vec!["d"]);

        let s3 = sg.edges[usize::from(s2)][&Symbol::Terminal(grm.terminal_off("u"))];
        assert_eq!(sg.states[usize::from(s3)].items.len(), 3);
        state_exists(&grm, &sg.states[usize::from(s3)], "Z", 0, 2, vec!["c"]);
        state_exists(&grm, &sg.states[usize::from(s3)], "W", 0, 1, vec!["d"]);
        state_exists(&grm, &sg.states[usize::from(s3)], "V", 0, 0, vec!["d"]);

        let s5 = sg.edges[usize::from(s4)][&Symbol::Nonterminal(grm.nonterminal_off("X"))];
        assert_eq!(sg.states[usize::from(s5)].items.len(), 2);
        state_exists(&grm, &sg.states[usize::from(s5)], "Y", 1, 2, vec!["d", "e"]);
        state_exists(&grm, &sg.states[usize::from(s5)], "T", 0, 2, vec!["a", "d", "e", "$"]);

        let s6 = sg.edges[usize::from(s5)][&Symbol::Terminal(grm.terminal_off("a"))];
        assert_eq!(sg.states[usize::from(s6)].items.len(), 1);
        state_exists(&grm, &sg.states[usize::from(s6)], "T", 0, 3, vec!["a", "d", "e", "$"]);

        let s8 = sg.edges[usize::from(s7)][&Symbol::Terminal(grm.terminal_off("t"))];
        assert_eq!(sg.states[usize::from(s8)].items.len(), 3);
        state_exists(&grm, &sg.states[usize::from(s8)], "Y", 0, 1, vec!["e"]);
        state_exists(&grm, &sg.states[usize::from(s8)], "Z", 0, 1, vec!["d"]);
        state_exists(&grm, &sg.states[usize::from(s8)], "W", 0, 0, vec!["e"]);

        let s9 = sg.edges[usize::from(s8)][&Symbol::Terminal(grm.terminal_off("u"))];
        assert_eq!(sg.states[usize::from(s9)].items.len(), 3);
        state_exists(&grm, &sg.states[usize::from(s9)], "Z", 0, 2, vec!["d"]);
        state_exists(&grm, &sg.states[usize::from(s9)], "W", 0, 1, vec!["e"]);
        state_exists(&grm, &sg.states[usize::from(s3)], "V", 0, 0, vec!["d"]);

        // Ommitted successors from the graph in Fig.3

        // X-successor of S0
        let s0x = sg.edges[0][&Symbol::Nonterminal(grm.nonterminal_off("X"))];
        state_exists(&grm, &sg.states[usize::from(s0x)], "^", 0, 1, vec!["$"]);

        // Y-successor of S1 (and it's d-successor)
        let s1y = sg.edges[usize::from(s1)][&Symbol::Nonterminal(grm.nonterminal_off("Y"))];
        state_exists(&grm, &sg.states[usize::from(s1y)], "X", 0, 2, vec!["a", "d", "e", "$"]);
        let s1yd = sg.edges[usize::from(s1y)][&Symbol::Terminal(grm.terminal_off("d"))];
        state_exists(&grm, &sg.states[usize::from(s1yd)], "X", 0, 3, vec!["a", "d", "e", "$"]);

        // Z-successor of S1 (and it's successor)
        let s1z = sg.edges[usize::from(s1)][&Symbol::Nonterminal(grm.nonterminal_off("Z"))];
        state_exists(&grm, &sg.states[usize::from(s1z)], "X", 1, 2, vec!["a", "d", "e", "$"]);
        let s1zc = sg.edges[usize::from(s1z)][&Symbol::Terminal(grm.terminal_off("c"))];
        state_exists(&grm, &sg.states[usize::from(s1zc)], "X", 1, 3, vec!["a", "d", "e", "$"]);

        // T-successor of S1
        let s1t = sg.edges[usize::from(s1)][&Symbol::Nonterminal(grm.nonterminal_off("T"))];
        state_exists(&grm, &sg.states[usize::from(s1t)], "X", 2, 2, vec!["a", "d", "e", "$"]);

        // Y-successor of S7 (and it's d-successor)
        let s7y = sg.edges[usize::from(s7)][&Symbol::Nonterminal(grm.nonterminal_off("Y"))];
        state_exists(&grm, &sg.states[usize::from(s7y)], "X", 3, 2, vec!["a", "d", "e", "$"]);
        let s7ye = sg.edges[usize::from(s7y)][&Symbol::Terminal(grm.terminal_off("e"))];
        state_exists(&grm, &sg.states[usize::from(s7ye)], "X", 3, 3, vec!["a", "d", "e", "$"]);

        // Z-successor of S7 (and it's successor)
        let s7z = sg.edges[usize::from(s7)][&Symbol::Nonterminal(grm.nonterminal_off("Z"))];
        state_exists(&grm, &sg.states[usize::from(s7z)], "X", 4, 2, vec!["a", "d", "e", "$"]);
        let s7zd = sg.edges[usize::from(s7z)][&Symbol::Terminal(grm.terminal_off("d"))];
        state_exists(&grm, &sg.states[usize::from(s7zd)], "X", 4, 3, vec!["a", "d", "e", "$"]);

        // T-successor of S7
        let s7t = sg.edges[usize::from(s7)][&Symbol::Nonterminal(grm.nonterminal_off("T"))];
        state_exists(&grm, &sg.states[usize::from(s7t)], "X", 5, 2, vec!["a", "d", "e", "$"]);

        // W-successor of S2 and S8 (merged)
        let s8w = sg.edges[usize::from(s8)][&Symbol::Nonterminal(grm.nonterminal_off("W"))];
        assert_eq!(s8w, sg.edges[usize::from(s2)][&Symbol::Nonterminal(grm.nonterminal_off("W"))]);
        state_exists(&grm, &sg.states[usize::from(s8w)], "Y", 0, 2, vec!["d", "e"]);

        // V-successor of S3 and S9 (merged)
        let s9v = sg.edges[usize::from(s9)][&Symbol::Nonterminal(grm.nonterminal_off("V"))];
        assert_eq!(s9v, sg.edges[usize::from(s3)][&Symbol::Nonterminal(grm.nonterminal_off("V"))]);
        state_exists(&grm, &sg.states[usize::from(s9v)], "W", 0, 2, vec!["d", "e"]);
    }

    #[test]
    fn test_pager_graph_and_gc() {
        // The example from Pager's paper (in test_pager_graph) occasionally creates unreachable
        // states, depending on the non-determinism inherent in iterating over sets in our
        // implementation, causing the test to fail. This happens in roughly 1 every 100 executions
        // if GC isn't present. So we run this test a lot of times on the basis that if the GC
        // fails to work correctly, this will eventually trigger.
        //
        // It goes without saying that this is not the ideal way of testing this, but if you can
        // distil this down to a small, deterministic example, you're a better person than I am.
        let grm = grammar_pager();
        for _ in 0..750 {
            test_pager_graph(&grm);
        }
    }
}
