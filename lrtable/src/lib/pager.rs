use std::{
    collections::{hash_map::HashMap, HashSet},
    hash::Hash,
};

use cfgrammar::{yacc::YaccGrammar, SIdx, Symbol};
use num_traits::{AsPrimitive, PrimInt, Unsigned, Zero};
use vob::Vob;

use crate::{itemset::Itemset, stategraph::StateGraph, StIdx, StIdxStorageT};

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

impl<StorageT: Hash + PrimInt + Unsigned> Itemset<StorageT> {
    /// Return true if `other` is weakly compatible with `self`.
    fn weakly_compatible(&self, other: &Self) -> bool {
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
        for &(pidx, dot) in self.items.keys() {
            if other.items.get(&(pidx, dot)).is_none() {
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
                if !(vob_intersect(&self.items[*i_key], &other.items[*j_key])
                    || vob_intersect(&self.items[*j_key], &other.items[*i_key]))
                {
                    continue;
                }
                // Conditions 2 and 3 in the Pager paper
                if vob_intersect(&self.items[*i_key], &self.items[*j_key])
                    || vob_intersect(&other.items[*i_key], &other.items[*j_key])
                {
                    continue;
                }
                return false;
            }
        }

        true
    }

    /// Merge `other` into `self`, returning `true` if this led to any changes. If `other` is not
    /// weakly compatible with `self`, this function's effects and return value are undefined.
    fn weakly_merge(&mut self, other: &Self) -> bool {
        let mut changed = false;
        for (&(pidx, dot), ctx) in &mut self.items {
            if ctx.or(&other.items[&(pidx, dot)]) {
                changed = true;
            }
        }
        changed
    }
}

/// Returns true if two identically sized bitvecs intersect.
fn vob_intersect(v1: &Vob, v2: &Vob) -> bool {
    // Iterating over integer sized blocks allows us to do this operation very quickly. Note that
    // the Vob implementation guarantees that the last block's unused bits will be zeroed out.
    for (b1, b2) in v1.iter_storage().zip(v2.iter_storage()) {
        if b1 & b2 != 0 {
            return true;
        }
    }
    false
}

/// Create a `StateGraph` from 'grm'.
pub fn pager_stategraph<StorageT: 'static + Hash + PrimInt + Unsigned>(
    grm: &YaccGrammar<StorageT>,
) -> StateGraph<StorageT>
where
    usize: AsPrimitive<StorageT>,
{
    // This function can be seen as a modified version of items() from Chen's dissertation.

    let firsts = grm.firsts();
    // closed_states and core_states are both equally sized vectors of states. Core states are
    // smaller, and used for the weakly compatible checks, but we ultimately need to return
    // closed states. Closed states which are None are those which require processing; thus
    // closed_states also implicitly serves as a todo list.
    let mut closed_states = Vec::new();
    let mut core_states = Vec::new();
    let mut edges: Vec<HashMap<Symbol<StorageT>, StIdx>> = Vec::new();

    let start_state = StIdx::from(StIdxStorageT::zero());
    let mut state0 = Itemset::new(grm);
    let mut ctx = Vob::from_elem(usize::from(grm.tokens_len()), false);
    ctx.set(usize::from(grm.eof_token_idx()), true);
    state0.add(grm.start_prod(), SIdx(StorageT::zero()), &ctx);
    closed_states.push(None);
    core_states.push(state0);
    edges.push(HashMap::new());

    // We maintain two lists of which rules and tokens we've seen; when processing a given
    // state there's no point processing a rule or token more than once.
    let mut seen_rules = Vob::from_elem(usize::from(grm.rules_len()), false);
    let mut seen_tokens = Vob::from_elem(usize::from(grm.tokens_len()), false);
    // new_states is used to separate out iterating over states vs. mutating it
    let mut new_states = Vec::new();
    // cnd_[rule|token]_weaklies represent which states are possible weakly compatible
    // matches for a given symbol.
    let mut cnd_rule_weaklies: Vec<Vec<StIdx>> = vec![Vec::new(); usize::from(grm.rules_len())];
    let mut cnd_token_weaklies: Vec<Vec<StIdx>> =
        vec![Vec::new(); usize::from(grm.tokens_len()).checked_add(1).unwrap()];

    let mut todo = 1; // How many None values are there in closed_states?
    let mut todo_off = 0; // Offset in closed states to start searching for the next todo.
    while todo > 0 {
        debug_assert_eq!(core_states.len(), closed_states.len());
        // state_i is the next item to process. We don't want to continually search for the
        // next None from the beginning, so we remember where we last saw a None (todo_off) and
        // search from that point onwards, wrapping as necessary. Since processing a state x
        // disproportionately causes state x + 1 to require processing, this prevents the
        // search from becoming horribly non-linear.
        let state_i = match closed_states
            .iter()
            .skip(todo_off)
            .position(Option::is_none)
        {
            Some(i) => todo_off + i,
            None => closed_states.iter().position(Option::is_none).unwrap(),
        };
        todo_off = state_i + 1;
        todo -= 1;

        {
            closed_states[state_i] = Some(core_states[state_i].close(grm, &firsts));
            let cl_state = &closed_states[state_i].as_ref().unwrap();
            seen_rules.set_all(false);
            seen_tokens.set_all(false);
            for &(pidx, dot) in cl_state.items.keys() {
                let prod = grm.prod(pidx);
                if dot == grm.prod_len(pidx) {
                    continue;
                }
                let sym = prod[usize::from(dot)];
                match sym {
                    Symbol::Rule(s_ridx) => {
                        if seen_rules[usize::from(s_ridx)] {
                            continue;
                        }
                        seen_rules.set(usize::from(s_ridx), true);
                    }
                    Symbol::Token(s_tidx) => {
                        if seen_tokens[usize::from(s_tidx)] {
                            continue;
                        }
                        seen_tokens.set(usize::from(s_tidx), true);
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
                    Symbol::Rule(s_ridx) => &cnd_rule_weaklies[usize::from(s_ridx)],
                    Symbol::Token(s_tidx) => &cnd_token_weaklies[usize::from(s_tidx)],
                };
                // First of all see if any of the candidate states are exactly the same as the
                // new state, in which case we only need to add an edge to the candidate
                // state. This isn't just an optimisation (though it does avoid the expense
                // of change propagation), but has a correctness aspect: there's no guarantee
                // that the weakly compatible check is reflexive (i.e. a state may not be
                // weakly compatible with itself).
                for cnd in cnd_states.iter().cloned() {
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
                }
                None => {
                    assert!(core_states.len() <= usize::from(StIdxStorageT::max_value()));
                    // The assert above guarantees that the cast below is safe.
                    let stidx = StIdx(core_states.len() as StIdxStorageT);
                    match sym {
                        Symbol::Rule(s_ridx) => {
                            cnd_rule_weaklies[usize::from(s_ridx)].push(stidx);
                        }
                        Symbol::Token(s_tidx) => {
                            cnd_token_weaklies[usize::from(s_tidx)].push(stidx);
                        }
                    }
                    edges[state_i].insert(sym, stidx);
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
    debug_assert_eq!(core_states.len(), closed_states.len());
    let (gc_states, gc_edges) = gc(
        core_states
            .drain(..)
            .zip(closed_states.drain(..).map(Option::unwrap))
            .collect(),
        start_state,
        edges,
    );
    StateGraph::new(gc_states, start_state, gc_edges)
}

/// Garbage collect `zip_states` (of `(core_states, closed_state)`) and `edges`. Returns a new pair
/// with unused states and their corresponding edges removed.
fn gc<StorageT: Eq + Hash + PrimInt>(
    mut states: Vec<(Itemset<StorageT>, Itemset<StorageT>)>,
    start_state: StIdx,
    mut edges: Vec<HashMap<Symbol<StorageT>, StIdx>>,
) -> (
    Vec<(Itemset<StorageT>, Itemset<StorageT>)>,
    Vec<HashMap<Symbol<StorageT>, StIdx>>,
) {
    // First of all, do a simple pass over all states. All state indexes reachable from the
    // start state will be inserted into the 'seen' set.
    let mut todo = HashSet::new();
    todo.insert(start_state);
    let mut seen = HashSet::new();
    while !todo.is_empty() {
        // XXX This is the clumsy way we're forced to do what we'd prefer to be:
        //     "let &(pidx, dot) = todo.pop()"
        let state_i = *todo.iter().next().unwrap();
        todo.remove(&state_i);
        seen.insert(state_i);

        todo.extend(
            edges[usize::from(state_i)]
                .values()
                .filter(|x| !seen.contains(x)),
        );
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
    let mut offsets = Vec::with_capacity(states.len());
    let mut offset = 0;
    for (state_i, zstate) in states
        .drain(..)
        .enumerate()
        // edges goes from 0..states_len(), and we know the latter can safely fit into an
        // StIdxStorageT, so the cast is safe.
        .map(|(x, y)| (StIdx(x as StIdxStorageT), y))
    {
        // state_i <= states_len(), which fits in StIdxStorageT, so state_i - offset must also be
        // <= states_len, making the cast safe
        offsets.push(StIdx((usize::from(state_i) - offset) as StIdxStorageT));
        if !seen.contains(&state_i) {
            offset += 1;
            continue;
        }
        gc_states.push(zstate);
    }

    // At this point the offsets list will be [0, 1, 1]. We now create new edges where each
    // offset is corrected by looking it up in the offsets list.
    let mut gc_edges = Vec::with_capacity(seen.len());
    for (st_edge_i, st_edges) in edges
        .drain(..)
        .enumerate()
        // edges goes from 0..states_len(), and we know the latter can safely fit into an
        // StIdxStorageT, so the cast is safe.
        .map(|(x, y)| (StIdx(x as StIdxStorageT), y))
    {
        if !seen.contains(&st_edge_i) {
            continue;
        }
        gc_edges.push(
            st_edges
                .iter()
                .map(|(&k, &v)| (k, offsets[usize::from(v)]))
                .collect(),
        );
    }

    (gc_states, gc_edges)
}

#[cfg(test)]
mod test {
    use vob::Vob;

    use crate::{pager::pager_stategraph, stategraph::state_exists, StIdx};
    use cfgrammar::{
        yacc::{YaccGrammar, YaccKind, YaccOriginalActionKind},
        SIdx, Symbol,
    };

    use super::vob_intersect;

    #[test]
    fn test_vob_intersect() {
        let mut b1 = Vob::from_elem(8, false);
        let mut b2 = Vob::from_elem(8, false);
        assert!(!vob_intersect(&b1, &b2));
        // Check that partial blocks (i.e. when only part of a word is used in the bitvec for
        // storage) maintain the expected guarantees.
        b1.push(false);
        b2.push(false);
        assert!(!vob_intersect(&b1, &b2));
        b1.push(true);
        b2.push(true);
        assert!(vob_intersect(&b1, &b2));

        b1 = Vob::from_elem(64, false);
        b2 = Vob::from_elem(64, false);
        b1.push(true);
        b2.push(true);
        for _ in 0..63 {
            b1.push(false);
            b2.push(false);
        }
        assert!(vob_intersect(&b1, &b2));
    }

    // GrammarAST from 'LR(k) Analyse fuer Pragmatiker'
    // Z : S
    // S : Sb
    //     bAa
    // A : aSc
    //     a
    //     aSb
    fn grammar3() -> YaccGrammar {
        YaccGrammar::new(
            YaccKind::Original(YaccOriginalActionKind::GenericParseTree),
            &"
          %start S
          %token a b c d
          %%
          S: S 'b' | 'b' A 'a';
          A: 'a' S 'c' | 'a' | 'a' S 'b';
          ",
        )
        .unwrap()
    }

    #[test]
    #[rustfmt::skip]
    fn test_stategraph() {
        let grm = grammar3();
        let sg = pager_stategraph(&grm);

        assert_eq!(sg.all_states_len(), StIdx(10));
        assert_eq!(sg.all_edges_len(), 10);

        assert_eq!(sg.closed_state(sg.start_state()).items.len(), 3);
        state_exists(&grm, &sg.closed_state(sg.start_state()), "^", 0, SIdx(0), vec!["$"]);
        state_exists(&grm, &sg.closed_state(sg.start_state()), "S", 0, SIdx(0), vec!["$", "b"]);
        state_exists(&grm, &sg.closed_state(sg.start_state()), "S", 1, SIdx(0), vec!["$", "b"]);

        let s1 = sg.edge(sg.start_state(), Symbol::Rule(grm.rule_idx("S").unwrap())).unwrap();
        assert_eq!(sg.closed_state(s1).items.len(), 2);
        state_exists(&grm, &sg.closed_state(s1), "^", 0, SIdx(1), vec!["$"]);
        state_exists(&grm, &sg.closed_state(s1), "S", 0, SIdx(1), vec!["$", "b"]);

        let s2 = sg.edge(s1, Symbol::Token(grm.token_idx("b").unwrap())).unwrap();
        assert_eq!(sg.closed_state(s2).items.len(), 1);
        state_exists(&grm, &sg.closed_state(s2), "S", 0, SIdx(2), vec!["$", "b"]);

        let s3 = sg.edge(sg.start_state(), Symbol::Token(grm.token_idx("b").unwrap())).unwrap();
        assert_eq!(sg.closed_state(s3).items.len(), 4);
        state_exists(&grm, &sg.closed_state(s3), "S", 1, SIdx(1), vec!["$", "b", "c"]);
        state_exists(&grm, &sg.closed_state(s3), "A", 0, SIdx(0), vec!["a"]);
        state_exists(&grm, &sg.closed_state(s3), "A", 1, SIdx(0), vec!["a"]);
        state_exists(&grm, &sg.closed_state(s3), "A", 2, SIdx(0), vec!["a"]);

        let s4 = sg.edge(s3, Symbol::Rule(grm.rule_idx("A").unwrap())).unwrap();
        assert_eq!(sg.closed_state(s4).items.len(), 1);
        state_exists(&grm, &sg.closed_state(s4), "S", 1, SIdx(2), vec!["$", "b", "c"]);

        let s5 = sg.edge(s4, Symbol::Token(grm.token_idx("a").unwrap())).unwrap();
        assert_eq!(sg.closed_state(s5).items.len(), 1);
        state_exists(&grm, &sg.closed_state(s5), "S", 1, SIdx(3), vec!["$", "b", "c"]);

        let s6 = sg.edge(s3, Symbol::Token(grm.token_idx("a").unwrap())).unwrap();
        // result from merging 10 into 3
        assert_eq!(s3, sg.edge(s6, Symbol::Token(grm.token_idx("b").unwrap())).unwrap());
        assert_eq!(sg.closed_state(s6).items.len(), 5);
        state_exists(&grm, &sg.closed_state(s6), "A", 0, SIdx(1), vec!["a"]);
        state_exists(&grm, &sg.closed_state(s6), "A", 1, SIdx(1), vec!["a"]);
        state_exists(&grm, &sg.closed_state(s6), "A", 2, SIdx(1), vec!["a"]);
        state_exists(&grm, &sg.closed_state(s6), "S", 0, SIdx(0), vec!["b", "c"]);
        state_exists(&grm, &sg.closed_state(s6), "S", 1, SIdx(0), vec!["b", "c"]);

        let s7 = sg.edge(s6, Symbol::Rule(grm.rule_idx("S").unwrap())).unwrap();
        assert_eq!(sg.closed_state(s7).items.len(), 3);
        state_exists(&grm, &sg.closed_state(s7), "A", 0, SIdx(2), vec!["a"]);
        state_exists(&grm, &sg.closed_state(s7), "A", 2, SIdx(2), vec!["a"]);
        state_exists(&grm, &sg.closed_state(s7), "S", 0, SIdx(1), vec!["b", "c"]);

        let s8 = sg.edge(s7, Symbol::Token(grm.token_idx("c").unwrap())).unwrap();
        assert_eq!(sg.closed_state(s8).items.len(), 1);
        state_exists(&grm, &sg.closed_state(s8), "A", 0, SIdx(3), vec!["a"]);

        let s9 = sg.edge(s7, Symbol::Token(grm.token_idx("b").unwrap())).unwrap();
        assert_eq!(sg.closed_state(s9).items.len(), 2);
        state_exists(&grm, &sg.closed_state(s9), "A", 2, SIdx(3), vec!["a"]);
        state_exists(&grm, &sg.closed_state(s9), "S", 0, SIdx(2), vec!["b", "c"]);
    }

    // Pager grammar
    fn grammar_pager() -> YaccGrammar {
        YaccGrammar::new(
            YaccKind::Original(YaccOriginalActionKind::GenericParseTree),
            &"
            %start X
            %%
             X : 'a' Y 'd' | 'a' Z 'c' | 'a' T | 'b' Y 'e' | 'b' Z 'd' | 'b' T;
             Y : 't' W | 'u' X;
             Z : 't' 'u';
             T : 'u' X 'a';
             W : 'u' V;
             V : ;
          ",
        )
        .unwrap()
    }

    #[rustfmt::skip]
    fn test_pager_graph(grm: &YaccGrammar) {
        let sg = pager_stategraph(&grm);

        assert_eq!(sg.all_states_len(), StIdx(23));
        assert_eq!(sg.all_edges_len(), 27);

        // State 0
        assert_eq!(sg.closed_state(sg.start_state()).items.len(), 7);
        state_exists(&grm, &sg.closed_state(sg.start_state()), "^", 0, SIdx(0), vec!["$"]);
        state_exists(&grm, &sg.closed_state(sg.start_state()), "X", 0, SIdx(0), vec!["$"]);
        state_exists(&grm, &sg.closed_state(sg.start_state()), "X", 1, SIdx(0), vec!["$"]);
        state_exists(&grm, &sg.closed_state(sg.start_state()), "X", 2, SIdx(0), vec!["$"]);
        state_exists(&grm, &sg.closed_state(sg.start_state()), "X", 3, SIdx(0), vec!["$"]);
        state_exists(&grm, &sg.closed_state(sg.start_state()), "X", 4, SIdx(0), vec!["$"]);
        state_exists(&grm, &sg.closed_state(sg.start_state()), "X", 5, SIdx(0), vec!["$"]);

        let s1 = sg.edge(sg.start_state(), Symbol::Token(grm.token_idx("a").unwrap())).unwrap();
        assert_eq!(sg.closed_state(s1).items.len(), 7);
        state_exists(&grm, &sg.closed_state(s1), "X", 0, SIdx(1), vec!["a", "d", "e", "$"]);
        state_exists(&grm, &sg.closed_state(s1), "X", 1, SIdx(1), vec!["a", "d", "e", "$"]);
        state_exists(&grm, &sg.closed_state(s1), "X", 2, SIdx(1), vec!["a", "d", "e", "$"]);
        state_exists(&grm, &sg.closed_state(s1), "Y", 0, SIdx(0), vec!["d"]);
        state_exists(&grm, &sg.closed_state(s1), "Y", 1, SIdx(0), vec!["d"]);
        state_exists(&grm, &sg.closed_state(s1), "Z", 0, SIdx(0), vec!["c"]);
        state_exists(&grm, &sg.closed_state(s1), "T", 0, SIdx(0), vec!["a", "d", "e", "$"]);

        let s7 = sg.edge(sg.start_state(), Symbol::Token(grm.token_idx("b").unwrap())).unwrap();
        assert_eq!(sg.closed_state(s7).items.len(), 7);
        state_exists(&grm, &sg.closed_state(s7), "X", 3, SIdx(1), vec!["a", "d", "e", "$"]);
        state_exists(&grm, &sg.closed_state(s7), "X", 4, SIdx(1), vec!["a", "d", "e", "$"]);
        state_exists(&grm, &sg.closed_state(s7), "X", 5, SIdx(1), vec!["a", "d", "e", "$"]);
        state_exists(&grm, &sg.closed_state(s1), "Y", 0, SIdx(0), vec!["d"]);
        state_exists(&grm, &sg.closed_state(s1), "Y", 1, SIdx(0), vec!["d"]);
        state_exists(&grm, &sg.closed_state(s1), "Z", 0, SIdx(0), vec!["c"]);
        state_exists(&grm, &sg.closed_state(s1), "T", 0, SIdx(0), vec!["a", "d", "e", "$"]);

        let s4 = sg.edge(s1, Symbol::Token(grm.token_idx("u").unwrap())).unwrap();
        assert_eq!(sg.closed_state(s4).items.len(), 8);
        assert_eq!(s4, sg.edge(s7, Symbol::Token(grm.token_idx("u").unwrap())).unwrap());
        state_exists(&grm, &sg.closed_state(s4), "Y", 1, SIdx(1), vec!["d", "e"]);
        state_exists(&grm, &sg.closed_state(s4), "T", 0, SIdx(1), vec!["a", "d", "e", "$"]);
        state_exists(&grm, &sg.closed_state(s4), "X", 0, SIdx(0), vec!["a", "d", "e"]);
        state_exists(&grm, &sg.closed_state(s4), "X", 1, SIdx(0), vec!["a", "d", "e"]);
        state_exists(&grm, &sg.closed_state(s4), "X", 2, SIdx(0), vec!["a", "d", "e"]);
        state_exists(&grm, &sg.closed_state(s4), "X", 3, SIdx(0), vec!["a", "d", "e"]);
        state_exists(&grm, &sg.closed_state(s4), "X", 4, SIdx(0), vec!["a", "d", "e"]);
        state_exists(&grm, &sg.closed_state(s4), "X", 5, SIdx(0), vec!["a", "d", "e"]);

        assert_eq!(s1, sg.edge(s4, Symbol::Token(grm.token_idx("a").unwrap())).unwrap());
        assert_eq!(s7, sg.edge(s4, Symbol::Token(grm.token_idx("b").unwrap())).unwrap());

        let s2 = sg.edge(s1, Symbol::Token(grm.token_idx("t").unwrap())).unwrap();
        assert_eq!(sg.closed_state(s2).items.len(), 3);
        state_exists(&grm, &sg.closed_state(s2), "Y", 0, SIdx(1), vec!["d"]);
        state_exists(&grm, &sg.closed_state(s2), "Z", 0, SIdx(1), vec!["c"]);
        state_exists(&grm, &sg.closed_state(s2), "W", 0, SIdx(0), vec!["d"]);

        let s3 = sg.edge(s2, Symbol::Token(grm.token_idx("u").unwrap())).unwrap();
        assert_eq!(sg.closed_state(s3).items.len(), 3);
        state_exists(&grm, &sg.closed_state(s3), "Z", 0, SIdx(2), vec!["c"]);
        state_exists(&grm, &sg.closed_state(s3), "W", 0, SIdx(1), vec!["d"]);
        state_exists(&grm, &sg.closed_state(s3), "V", 0, SIdx(0), vec!["d"]);

        let s5 = sg.edge(s4, Symbol::Rule(grm.rule_idx("X").unwrap())).unwrap();
        assert_eq!(sg.closed_state(s5).items.len(), 2);
        state_exists(&grm, &sg.closed_state(s5), "Y", 1, SIdx(2), vec!["d", "e"]);
        state_exists(&grm, &sg.closed_state(s5), "T", 0, SIdx(2), vec!["a", "d", "e", "$"]);

        let s6 = sg.edge(s5, Symbol::Token(grm.token_idx("a").unwrap())).unwrap();
        assert_eq!(sg.closed_state(s6).items.len(), 1);
        state_exists(&grm, &sg.closed_state(s6), "T", 0, SIdx(3), vec!["a", "d", "e", "$"]);

        let s8 = sg.edge(s7, Symbol::Token(grm.token_idx("t").unwrap())).unwrap();
        assert_eq!(sg.closed_state(s8).items.len(), 3);
        state_exists(&grm, &sg.closed_state(s8), "Y", 0, SIdx(1), vec!["e"]);
        state_exists(&grm, &sg.closed_state(s8), "Z", 0, SIdx(1), vec!["d"]);
        state_exists(&grm, &sg.closed_state(s8), "W", 0, SIdx(0), vec!["e"]);

        let s9 = sg.edge(s8, Symbol::Token(grm.token_idx("u").unwrap())).unwrap();
        assert_eq!(sg.closed_state(s9).items.len(), 3);
        state_exists(&grm, &sg.closed_state(s9), "Z", 0, SIdx(2), vec!["d"]);
        state_exists(&grm, &sg.closed_state(s9), "W", 0, SIdx(1), vec!["e"]);
        state_exists(&grm, &sg.closed_state(s3), "V", 0, SIdx(0), vec!["d"]);

        // Ommitted successors from the graph in Fig.3

        // X-successor of S0
        let s0x = sg.edge(sg.start_state(), Symbol::Rule(grm.rule_idx("X").unwrap())).unwrap();
        state_exists(&grm, &sg.closed_state(s0x), "^", 0, SIdx(1), vec!["$"]);

        // Y-successor of S1 (and it's d-successor)
        let s1y = sg.edge(s1, Symbol::Rule(grm.rule_idx("Y").unwrap())).unwrap();
        state_exists(&grm, &sg.closed_state(s1y), "X", 0, SIdx(2), vec!["a", "d", "e", "$"]);
        let s1yd = sg.edge(s1y, Symbol::Token(grm.token_idx("d").unwrap())).unwrap();
        state_exists(&grm, &sg.closed_state(s1yd), "X", 0, SIdx(3), vec!["a", "d", "e", "$"]);

        // Z-successor of S1 (and it's successor)
        let s1z = sg.edge(s1, Symbol::Rule(grm.rule_idx("Z").unwrap())).unwrap();
        state_exists(&grm, &sg.closed_state(s1z), "X", 1, SIdx(2), vec!["a", "d", "e", "$"]);
        let s1zc = sg.edge(s1z, Symbol::Token(grm.token_idx("c").unwrap())).unwrap();
        state_exists(&grm, &sg.closed_state(s1zc), "X", 1, SIdx(3), vec!["a", "d", "e", "$"]);

        // T-successor of S1
        let s1t = sg.edge(s1, Symbol::Rule(grm.rule_idx("T").unwrap())).unwrap();
        state_exists(&grm, &sg.closed_state(s1t), "X", 2, SIdx(2), vec!["a", "d", "e", "$"]);

        // Y-successor of S7 (and it's d-successor)
        let s7y = sg.edge(s7, Symbol::Rule(grm.rule_idx("Y").unwrap())).unwrap();
        state_exists(&grm, &sg.closed_state(s7y), "X", 3, SIdx(2), vec!["a", "d", "e", "$"]);
        let s7ye = sg.edge(s7y, Symbol::Token(grm.token_idx("e").unwrap())).unwrap();
        state_exists(&grm, &sg.closed_state(s7ye), "X", 3, SIdx(3), vec!["a", "d", "e", "$"]);

        // Z-successor of S7 (and it's successor)
        let s7z = sg.edge(s7, Symbol::Rule(grm.rule_idx("Z").unwrap())).unwrap();
        state_exists(&grm, &sg.closed_state(s7z), "X", 4, SIdx(2), vec!["a", "d", "e", "$"]);
        let s7zd = sg.edge(s7z, Symbol::Token(grm.token_idx("d").unwrap())).unwrap();
        state_exists(&grm, &sg.closed_state(s7zd), "X", 4, SIdx(3), vec!["a", "d", "e", "$"]);

        // T-successor of S7
        let s7t = sg.edge(s7, Symbol::Rule(grm.rule_idx("T").unwrap())).unwrap();
        state_exists(&grm, &sg.closed_state(s7t), "X", 5, SIdx(2), vec!["a", "d", "e", "$"]);

        // W-successor of S2 and S8 (merged)
        let s8w = sg.edge(s8, Symbol::Rule(grm.rule_idx("W").unwrap())).unwrap();
        assert_eq!(s8w, sg.edge(s2, Symbol::Rule(grm.rule_idx("W").unwrap())).unwrap());
        state_exists(&grm, &sg.closed_state(s8w), "Y", 0, SIdx(2), vec!["d", "e"]);

        // V-successor of S3 and S9 (merged)
        let s9v = sg.edge(s9, Symbol::Rule(grm.rule_idx("V").unwrap())).unwrap();
        assert_eq!(s9v, sg.edge(s3, Symbol::Rule(grm.rule_idx("V").unwrap())).unwrap());
        state_exists(&grm, &sg.closed_state(s9v), "W", 0, SIdx(2), vec!["d", "e"]);
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

    #[test]
    #[rustfmt::skip]
    fn test_pager_graph_core_states() {
        let grm = grammar_pager();
        let sg = pager_stategraph(&grm);

        // State 0
        assert_eq!(sg.core_state(sg.start_state()).items.len(), 1);
        state_exists(&grm, &sg.core_state(sg.start_state()), "^", 0, SIdx(0), vec!["$"]);
    }
}
