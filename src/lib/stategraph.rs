use std::collections::HashSet;
use std::collections::hash_map::{Entry, HashMap};
use std::hash::BuildHasherDefault;

extern crate bit_vec;
use self::bit_vec::{BitBlock, BitVec};

extern crate fnv;
use self::fnv::FnvHasher;

use StIdx;
use grammar::{PIdx, Grammar, NTIdx, Symbol, SIdx, TIdx};

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


/// The type of "context" (also known as "lookaheads")
pub type Ctx = BitVec;

/// Firsts stores all the first sets for a given grammar.
///
/// # Example
/// Given a grammar `input`:
///
/// ```c
/// S : A "b";
/// A : "a" |;
/// ```
///
/// ```c
/// let grm = Grammar::new(parse_yacc(&input));
/// let firsts = Firsts::new(grm);
/// ```
///
/// Then the following assertions (and only the following assertions) about the firsts set are
/// correct:
/// ```c
/// assert!(firsts.is_set(grm.nonterminal_off("S"), grm.terminal_off("a")));
/// assert!(firsts.is_set(grm.nonterminal_off("S"), grm.terminal_off("b")));
/// assert!(firsts.is_epsilon_set(grm.nonterminal_off("S")));
/// assert!(firsts.is_set(grm.nonterminal_off("A"), grm.terminal_off("a")));
/// assert!(firsts.is_epsilon_set(grm.nonterminal_off("A")));
/// ```
#[derive(Debug)]
struct Firsts {
    // The representation is a contiguous bitfield, of (terms_len * 1) * nonterms_len. Put another
    // way, each nonterminal has (terms_len + 1) bits, where the bit at position terms_len
    // represents epsilon. So for the grammar given above, the bitvector would be two sequences of
    // 3 bits where bits 0, 1, 2 represent terminals a, b, epsilon respectively.
    //   111101
    // Where "111" is for the nonterminal S, and 101 for A.
    prod_firsts: Vec<Ctx>,
    prod_epsilons: BitVec,
    terms_len: usize
}

impl Firsts {
    /// Generates and returns the firsts set for the given grammar.
    fn new(grm: &Grammar) -> Firsts {
        let mut prod_firsts = Vec::with_capacity(grm.nonterms_len);
        for _ in 0..grm.nonterms_len {
            prod_firsts.push(BitVec::from_elem(grm.terms_len, false));
        }
        let mut firsts = Firsts {
            prod_firsts  : prod_firsts,
            prod_epsilons: BitVec::from_elem(grm.nonterms_len, false),
            terms_len   : grm.terms_len
        };

        // Loop looking for changes to the firsts set, until we reach a fixed point. In essence, we
        // look at each rule E, and see if any of the nonterminals at the start of its productions
        // have new elements in since we last looked. If they do, we'll have to do another round.
        loop {
            let mut changed = false;
            for rul_i in grm.iter_nonterm_idxs() {
                // For each rule E
                for prod_i in grm.nonterm_to_prods(rul_i).unwrap().iter() {
                    // ...and each production A
                    let prod = grm.prod(*prod_i).unwrap();
                    if prod.is_empty() {
                        // if it's an empty production, ensure this nonterminal's epsilon bit is
                        // set.
                        if !firsts.is_epsilon_set(NTIdx::from(rul_i)) {
                            firsts.prod_epsilons.set(usize::from(rul_i), true);
                            changed = true;
                        }
                        continue;
                    }
                    for (sym_i, sym) in prod.iter().enumerate() {
                        match *sym {
                            Symbol::Terminal(term_i) => {
                                // if symbol is a Terminal, add to FIRSTS
                                if !firsts.set(rul_i, term_i) {
                                    changed = true;
                                }
                                break;
                            },
                            Symbol::Nonterminal(nonterm_i) => {
                                // if we're dealing with another Nonterminal, union its FIRSTs
                                // together with the current nonterminals FIRSTs. Note this is
                                // (intentionally) a no-op if the two terminals are one and the
                                // same.
                                for term_idx in grm.iter_term_idxs() {
                                    if firsts.is_set(nonterm_i, term_idx)
                                      && !firsts.set(rul_i, term_idx) {
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
            if !changed { return firsts; }
        }
    }

    /// Returns true if the terminal `tidx` is in the first set for nonterminal `nidx` is set.
    fn is_set(&self, nidx: NTIdx, tidx: TIdx) -> bool {
        self.prod_firsts[usize::from(nidx)][usize::from(tidx)]
    }

    /// Get all the firsts for production `nidx` as a `Ctx`.
    fn prod_firsts(&self, nidx: NTIdx) -> &Ctx {
        &self.prod_firsts[usize::from(usize::from(nidx))]
    }

    /// Returns true if the nonterminal `nidx` has epsilon in its first set.
    fn is_epsilon_set(&self, nidx: NTIdx) -> bool {
        self.prod_epsilons[usize::from(usize::from(nidx))]
    }

    /// Ensures that the firsts bit for terminal `tidx` nonterminal `nidx` is set. Returns true if
    /// it was already set, or false otherwise.
    fn set(&mut self, nidx: NTIdx, tidx: TIdx) -> bool {
        let mut prod = &mut self.prod_firsts[usize::from(nidx)];
        if prod[usize::from(tidx)] {
            true
        }
        else {
            prod.set(usize::from(tidx), true);
            false
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Itemset {
    pub items: HashMap<(PIdx, SIdx), Ctx, BuildHasherDefault<FnvHasher>>
}

impl Itemset {
    /// Create a blank Itemset.
    fn new(_: &Grammar) -> Itemset {
        Itemset {items: HashMap::with_hasher(BuildHasherDefault::<FnvHasher>::default())}
    }

    /// Add an item `(prod, dot)` with context `ctx` to this itemset. Returns true if this led to
    /// any changes in the itemset.
    fn add(&mut self, prod: PIdx, dot: SIdx, ctx: &Ctx) -> bool {
        let entry = self.items.entry((prod, dot));
        match entry {
            Entry::Occupied(mut e) => {
                e.get_mut().union(ctx)
            }
            Entry::Vacant(e)       => {
                e.insert(ctx.clone());
                true
            }
        }
    }

    /// Create a new itemset which is a closed version of `self`.
    fn close(&self, grm: &Grammar, firsts: &Firsts) -> Itemset {
        // This function can be seen as a merger of getClosure and getContext from Chen's
        // dissertation.

        let mut new_is = self.clone(); // The new itemset we're building up

        // In a typical description of this algorithm, one would have a todo set which contains
        // pairs (prod_i, dot). Unfortunately this is a slow way of doing things. Searching the set
        // for the next item and removing it is slow; and, since we don't know how many potential
        // dots there are in a production, the set is of potentially unbounded size, so we can end
        // up resizing memory. Since this function is the most expensive in the table generation,
        // using a HashSet (which is the "obvious" solution) is slow.
        //
        // However, we can reduce these costs through two observations:
        //   1) The initial todo set is populated with (prod_i, dot) pairs that all come from
        //      self.items.keys(). There's no point copying these into a todo list.
        //   2) All subsequent todo items are of the form (prod_off, 0). Since the dot in these
        //      cases is always 0, we don't need to store pairs: simply knowing which prod_off's we
        //      need to look at is sufficient. We can represent these with a fixed-size bitfield.
        // All we need to do is first iterate through the items in 1 and, when it's exhausted,
        // continually iterate over the bitfield from 2 until no new items have been added.

        let mut keys_iter = self.items.keys(); // The initial todo list
        type BitVecBitSize = u32; // As of 0.4.3, BitVec only supports u32 blocks
        let mut zero_todos = BitVec::<BitVecBitSize>::from_elem(grm.prods_len, false); // Subsequent todos
        let mut new_ctx = BitVec::from_elem(grm.terms_len, false);
        loop {
            let prod_i;
            let dot;
            // Find the next todo item or, if there are none, break the loop. First of all we try
            // pumping keys_iter for its next value. If there is none (i.e. we've exhausted that
            // part of the todo set), we iterate over zero_todos.
            match keys_iter.next() {
                Some(&(x, y)) => {
                    prod_i = x;
                    dot = y;
                }
                None => {
                    // Quickly iterate over the BitVec looking for the first non-zero word.
                    match zero_todos.blocks().enumerate().filter(|&(_, b)| b != 0).next() {
                        Some((b_off, b)) => {
                            // prod_i is the block offset plus the index of the first bit set.
                            prod_i = PIdx::from(b_off * BitVecBitSize::bits() + (b.trailing_zeros() as usize))
                        },
                        None => break
                    }
                    dot = SIdx::from(0);
                    zero_todos.set(prod_i.into(), false);
                }
            }
            let prod = grm.prod(prod_i).unwrap();
            if dot == SIdx::from(prod.len()) { continue; }
            if let Symbol::Nonterminal(nonterm_i) = prod[usize::from(dot)] {
                // This if statement is, in essence, a fast version of what's called getContext in
                // Chen's dissertation, folding in getTHeads at the same time. The particular
                // formulation here is based as much on
                // http://binarysculpting.com/2012/02/04/computing-lr1-closure/ as it is any of the
                // several versions of getTHeads in Chen's dissertation. Nevertheless, the mapping
                // between the two different formulations is fairly straight-forward.
                new_ctx.clear();
                let mut nullable = true;
                for sym in prod.iter().skip(usize::from(dot) + 1) {
                    match sym {
                        &Symbol::Terminal(term_j) => {
                            new_ctx.set(usize::from(term_j), true);
                            nullable = false;
                            break;
                        },
                        &Symbol::Nonterminal(nonterm_j) => {
                            new_ctx.union(firsts.prod_firsts(nonterm_j));
                            if !firsts.is_epsilon_set(nonterm_j) {
                                nullable = false;
                                break;
                            }
                        }
                    }
                }
                if nullable {
                    new_ctx.union(&new_is.items[&(prod_i, dot)]);
                }

                for ref_prod_i in grm.nonterm_to_prods(nonterm_i).unwrap().iter() {
                    if new_is.add(*ref_prod_i, SIdx::from(0), &new_ctx) {
                        zero_todos.set(usize::from(*ref_prod_i), true);
                    }
                }
            }
        }
        new_is
    }

    /// Create a new Itemset based on calculating the goto of 'sym' on the current Itemset.
    fn goto(&self, grm: &Grammar, sym: &Symbol) -> Itemset {
        // This is called 'transition' in Chen's dissertation, though note that the definition
        // therein appears to get the dot in the input/output the wrong way around.
        let mut newis = Itemset::new(grm);
        for (&(prod_i, dot), ctx) in &self.items {
            let prod = grm.prod(prod_i).unwrap();
            if dot == SIdx::from(prod.len()) { continue; }
            if sym == &prod[usize::from(dot)] {
                newis.add(prod_i, SIdx::from(usize::from(dot) + 1), ctx);
            }
        }
        newis
    }

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

pub struct StateGraph {
    /// A vector of states
    pub states: Vec<Itemset>,
    /// For each state in `states`, edges is a hashmap from symbols to state offsets.
    pub edges: Vec<HashMap<Symbol, StIdx>>
}

impl StateGraph {
    /// Create a StateGraph from 'grm'.
    pub fn new(grm: &Grammar) -> StateGraph {
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
        ctx.set(usize::from(grm.end_term), true);
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
                    if dot == SIdx::from(prod.len()) { continue; }
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

            for (sym, nstate) in new_states.drain(..) {
                let mut m = None;
                {
                    // Try and find a weakly compatible match for this state.
                    let cnd_weaklies = match sym {
                        Symbol::Nonterminal(nonterm_i) => &cnd_nonterm_weaklies[usize::from(nonterm_i)],
                        Symbol::Terminal(term_i) => &cnd_term_weaklies[usize::from(term_i)]
                    };
                    for cnd in cnd_weaklies.iter().map(|x| *x) {
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
        let (closed_states, edges) = StateGraph::gc(closed_states.drain(..)
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
}

#[cfg(test)]
mod test {
    extern crate bit_vec;
    use self::bit_vec::BitVec;

    use super::{bitvec_intersect, Itemset, Firsts, StateGraph};
    use grammar::{Grammar, SIdx, Symbol, TIdx};
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

    fn has(grm: &Grammar, firsts: &Firsts, rn: &str, should_be: Vec<&str>) {
        let nt_i = grm.nonterminal_off(rn);
        for i in 0 .. grm.terms_len {
            let n = grm.term_name(TIdx::from(i)).unwrap();
            match should_be.iter().position(|&x| x == n) {
                Some(_) => {
                    if !firsts.is_set(nt_i, TIdx::from(i)) {
                        panic!("{} is not set in {}", n, rn);
                    }
                }
                None    => {
                    if firsts.is_set(nt_i, TIdx::from(i)) {
                        panic!("{} is incorrectly set in {}", n, rn);
                    }
                }
            }
        }
        if should_be.iter().position(|x| x == &"".to_string()).is_some() {
            assert!(firsts.is_epsilon_set(nt_i));
        }
    }

    #[test]
    fn test_first(){
        let ast = parse_yacc(&"
          %start C
          %token c d
          %%
          C: 'c';
          D: 'd';
          E: D | C;
          F: E;
          ".to_string()).unwrap();
        let grm = Grammar::new(&ast);
        let firsts = Firsts::new(&grm);
        has(&grm, &firsts, "^", vec!["c"]);
        has(&grm, &firsts, "D", vec!["d"]);
        has(&grm, &firsts, "E", vec!["d", "c"]);
        has(&grm, &firsts, "F", vec!["d", "c"]);
    }

    #[test]
    fn test_first_no_subsequent_nonterminals() {
        let ast = parse_yacc(&"
          %start C
          %token c d
          %%
          C: 'c';
          D: 'd';
          E: D C;
          ".to_string()).unwrap();
        let grm = Grammar::new(&ast);
        let firsts = Firsts::new(&grm);
        has(&grm, &firsts, "E", vec!["d"]);
    }

    #[test]
    fn test_first_epsilon() {
        let ast = parse_yacc(&"
          %start A
          %token a b c
          %%
          A: B 'a';
          B: 'b' | ;
          C: 'c' | ;
          D: C;
          ".to_string()).unwrap();
        let grm = Grammar::new(&ast);
        let firsts = Firsts::new(&grm);
        has(&grm, &firsts, "A", vec!["b", "a"]);
        has(&grm, &firsts, "C", vec!["c", ""]);
        has(&grm, &firsts, "D", vec!["c", ""]);
    }

    #[test]
    fn test_last_epsilon() {
        let ast = parse_yacc(&"
          %start A
          %token b c
          %%
          A: B C;
          B: 'b' | ;
          C: B 'c' B;
          ".to_string()).unwrap();
        let grm = Grammar::new(&ast);
        let firsts = Firsts::new(&grm);
        has(&grm, &firsts, "A", vec!["b", "c"]);
        has(&grm, &firsts, "B", vec!["b", ""]);
        has(&grm, &firsts, "C", vec!["b", "c"]);
    }

    #[test]
    fn test_first_no_multiples() {
        let ast = parse_yacc(&"
          %start A
          %token b c
          %%
          A: B 'b';
          B: 'b' | ;
          ".to_string()).unwrap();
        let grm = Grammar::new(&ast);
        let firsts = Firsts::new(&grm);
        has(&grm, &firsts, "A", vec!["b"]);
    }

    fn eco_grammar() -> Grammar {
        let ast = parse_yacc(&"
          %start S
          %token a b c d f
          %%
          S: S 'b' | 'b' A 'a' | 'a';
          A: 'a' S 'c' | 'a' | 'a' S 'b';
          B: A S;
          C: D A;
          D: 'd' | ;
          F: C D 'f';
          ".to_string()).unwrap();
        Grammar::new(&ast)
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
        let ast = parse_yacc(&"
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
          ".to_string()).unwrap();
        let grm = Grammar::new(&ast);
        let firsts = Firsts::new(&grm);
        has(&grm, &firsts, "E", vec!["a"]);
        has(&grm, &firsts, "T", vec!["a"]);
        has(&grm, &firsts, "P", vec!["a"]);
        has(&grm, &firsts, "C", vec!["c", ""]);
        has(&grm, &firsts, "D", vec!["f", "d", ""]);
        has(&grm, &firsts, "G", vec!["c", "d", "f", ""]);
    }

    fn state_exists(grm: &Grammar, is: &Itemset, nt: &str, prod_off: usize, dot: usize, la:
                        Vec<&str>) {
        let ab_prod_off = grm.nonterm_to_prods(grm.nonterminal_off(nt)).unwrap()[prod_off];
        let ctx = &is.items[&(ab_prod_off, SIdx::from(dot))];
        for i in 0..grm.terms_len {
            let bit = ctx[i];
            let mut found = false;
            for t in la.iter() {
                if grm.terminal_off(t) == TIdx::from(i) {
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
                       grm.term_name(TIdx::from(i)).unwrap(), dot, prod_off, nt);
            }
        }
    }

    fn num_active_states(is: &Itemset) -> usize {
        is.items.len()
    }

    #[test]
    fn test_dragon_grammar() {
        // From http://binarysculpting.com/2012/02/04/computing-lr1-closure/
        let grm = Grammar::new(&parse_yacc(&"
          %start S
          %%
          S: L '=' R | R;
          L: '*' R | 'id';
          R: L;
          ".to_string()).unwrap());
        let firsts = Firsts::new(&grm);

        let mut is = Itemset::new(&grm);
        let mut la = BitVec::from_elem(grm.terms_len, false);
        la.set(usize::from(grm.terminal_off("$")), true);
        is.add(grm.nonterm_to_prods(grm.nonterminal_off("^")).unwrap()[0], SIdx::from(0), &la);
        let cls_is = is.close(&grm, &firsts);
        println!("{:?}", cls_is);
        assert_eq!(num_active_states(&cls_is), 6);
        state_exists(&grm, &cls_is, "^", 0, 0, vec!["$"]);
        state_exists(&grm, &cls_is, "S", 0, 0, vec!["$"]);
        state_exists(&grm, &cls_is, "S", 1, 0, vec!["$"]);
        state_exists(&grm, &cls_is, "L", 0, 0, vec!["$", "="]);
        state_exists(&grm, &cls_is, "L", 1, 0, vec!["$", "="]);
        state_exists(&grm, &cls_is, "R", 0, 0, vec!["$"]);
    }

    #[test]
    fn test_closure1_ecogrm() {
        let grm = eco_grammar();
        let firsts = Firsts::new(&grm);

        let mut is = Itemset::new(&grm);
        let mut la = BitVec::from_elem(grm.terms_len, false);
        la.set(usize::from(grm.terminal_off("$")), true);
        is.add(grm.nonterm_to_prods(grm.nonterminal_off("^")).unwrap()[0], SIdx::from(0), &la);
        let mut cls_is = is.close(&grm, &firsts);

        state_exists(&grm, &cls_is, "^", 0, 0, vec!["$"]);
        state_exists(&grm, &cls_is, "S", 0, 0, vec!["b", "$"]);
        state_exists(&grm, &cls_is, "S", 1, 0, vec!["b", "$"]);
        state_exists(&grm, &cls_is, "S", 2, 0, vec!["b", "$"]);

        is = Itemset::new(&grm);
        is.add(grm.nonterm_to_prods(grm.nonterminal_off("F")).unwrap()[0], SIdx::from(0), &la);
        cls_is = is.close(&grm, &firsts);
        state_exists(&grm, &cls_is, "F", 0, 0, vec!["$"]);
        state_exists(&grm, &cls_is, "C", 0, 0, vec!["d", "f"]);
        state_exists(&grm, &cls_is, "D", 0, 0, vec!["a"]);
        state_exists(&grm, &cls_is, "D", 1, 0, vec!["a"]);
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
    fn test_closure1_grm3() {
        let grm = grammar3();
        let firsts = Firsts::new(&grm);

        let mut is = Itemset::new(&grm);
        let mut la = BitVec::from_elem(grm.terms_len, false);
        la.set(usize::from(grm.terminal_off("$")), true);
        is.add(grm.nonterm_to_prods(grm.nonterminal_off("^")).unwrap()[0], SIdx::from(0), &la);
        let mut cls_is = is.close(&grm, &firsts);

        state_exists(&grm, &cls_is, "^", 0, 0, vec!["$"]);
        state_exists(&grm, &cls_is, "S", 0, 0, vec!["b", "$"]);
        state_exists(&grm, &cls_is, "S", 1, 0, vec!["b", "$"]);

        is = Itemset::new(&grm);
        la = BitVec::from_elem(grm.terms_len, false);
        la.set(usize::from(grm.terminal_off("b")), true);
        la.set(usize::from(grm.terminal_off("$")), true);
        is.add(grm.nonterm_to_prods(grm.nonterminal_off("S")).unwrap()[1], SIdx::from(1), &la);
        cls_is = is.close(&grm, &firsts);
        state_exists(&grm, &cls_is, "A", 0, 0, vec!["a"]);
        state_exists(&grm, &cls_is, "A", 1, 0, vec!["a"]);
        state_exists(&grm, &cls_is, "A", 2, 0, vec!["a"]);

        is = Itemset::new(&grm);
        la = BitVec::from_elem(grm.terms_len, false);
        la.set(usize::from(grm.terminal_off("a")), true);
        is.add(grm.nonterm_to_prods(grm.nonterminal_off("A")).unwrap()[0], SIdx::from(1), &la);
        cls_is = is.close(&grm, &firsts);
        state_exists(&grm, &cls_is, "S", 0, 0, vec!["b", "c"]);
        state_exists(&grm, &cls_is, "S", 1, 0, vec!["b", "c"]);
    }

    #[test]
    fn test_goto1() {
        let grm = grammar3();
        let firsts = Firsts::new(&grm);

        let mut is = Itemset::new(&grm);
        let mut la = BitVec::from_elem(grm.terms_len, false);
        la.set(usize::from(grm.terminal_off("$")), true);
        is.add(grm.nonterm_to_prods(grm.nonterminal_off("^")).unwrap()[0], SIdx::from(0), &la);
        let cls_is = is.close(&grm, &firsts);

        let goto1 = cls_is.goto(&grm, &Symbol::Nonterminal(grm.nonterminal_off("S")));
        state_exists(&grm, &goto1, "^", 0, 1, vec!["$"]);
        state_exists(&grm, &goto1, "S", 0, 1, vec!["$", "b"]);

        // follow 'b' from start set
        let goto2 = cls_is.goto(&grm, &Symbol::Terminal(grm.terminal_off("b")));
        state_exists(&grm, &goto2, "S", 1, 1, vec!["$", "b"]);

        // continue by following 'a' from last goto, after it's been closed
        let goto3 = goto2.close(&grm, &firsts).goto(&grm, &Symbol::Terminal(grm.terminal_off("a")));
        state_exists(&grm, &goto3, "A", 1, 1, vec!["a"]);
        state_exists(&grm, &goto3, "A", 2, 1, vec!["a"]);
    }

    #[test]
    fn test_stategraph() {
        let grm = grammar3();
        let sg = StateGraph::new(&grm);

        assert_eq!(sg.states.len(), 10);
        assert_eq!(sg.edges.iter().fold(0, |a, e| a + e.len()), 10);

        assert_eq!(num_active_states(&sg.states[0]), 3);
        state_exists(&grm, &sg.states[0], "^", 0, 0, vec!["$"]);
        state_exists(&grm, &sg.states[0], "S", 0, 0, vec!["$", "b"]);
        state_exists(&grm, &sg.states[0], "S", 1, 0, vec!["$", "b"]);

        let s1 = sg.edges[0][&Symbol::Nonterminal(grm.nonterminal_off("S"))];
        assert_eq!(num_active_states(&sg.states[usize::from(s1)]), 2);
        state_exists(&grm, &sg.states[usize::from(s1)], "^", 0, 1, vec!["$"]);
        state_exists(&grm, &sg.states[usize::from(s1)], "S", 0, 1, vec!["$", "b"]);

        let s2 = sg.edges[usize::from(s1)][&Symbol::Terminal(grm.terminal_off("b"))];
        assert_eq!(num_active_states(&sg.states[usize::from(s2)]), 1);
        state_exists(&grm, &sg.states[usize::from(s2)], "S", 0, 2, vec!["$", "b"]);

        let s3 = sg.edges[0][&Symbol::Terminal(grm.terminal_off("b"))];
        assert_eq!(num_active_states(&sg.states[usize::from(s3)]), 4);
        state_exists(&grm, &sg.states[usize::from(s3)], "S", 1, 1, vec!["$", "b", "c"]);
        state_exists(&grm, &sg.states[usize::from(s3)], "A", 0, 0, vec!["a"]);
        state_exists(&grm, &sg.states[usize::from(s3)], "A", 1, 0, vec!["a"]);
        state_exists(&grm, &sg.states[usize::from(s3)], "A", 2, 0, vec!["a"]);

        let s4 = sg.edges[usize::from(s3)][&Symbol::Nonterminal(grm.nonterminal_off("A"))];
        assert_eq!(num_active_states(&sg.states[usize::from(s4)]), 1);
        state_exists(&grm, &sg.states[usize::from(s4)], "S", 1, 2, vec!["$", "b", "c"]);

        let s5 = sg.edges[usize::from(s4)][&Symbol::Terminal(grm.terminal_off("a"))];
        assert_eq!(num_active_states(&sg.states[usize::from(s5)]), 1);
        state_exists(&grm, &sg.states[usize::from(s5)], "S", 1, 3, vec!["$", "b", "c"]);

        let s6 = sg.edges[usize::from(s3)][&Symbol::Terminal(grm.terminal_off("a"))];
        // result from merging 10 into 3
        assert_eq!(s3, sg.edges[usize::from(s6)][&Symbol::Terminal(grm.terminal_off("b"))]);
        assert_eq!(num_active_states(&sg.states[usize::from(s6)]), 5);
        state_exists(&grm, &sg.states[usize::from(s6)], "A", 0, 1, vec!["a"]);
        state_exists(&grm, &sg.states[usize::from(s6)], "A", 1, 1, vec!["a"]);
        state_exists(&grm, &sg.states[usize::from(s6)], "A", 2, 1, vec!["a"]);
        state_exists(&grm, &sg.states[usize::from(s6)], "S", 0, 0, vec!["b", "c"]);
        state_exists(&grm, &sg.states[usize::from(s6)], "S", 1, 0, vec!["b", "c"]);

        let s7 = sg.edges[usize::from(s6)][&Symbol::Nonterminal(grm.nonterminal_off("S"))];
        assert_eq!(num_active_states(&sg.states[usize::from(s7)]), 3);
        state_exists(&grm, &sg.states[usize::from(s7)], "A", 0, 2, vec!["a"]);
        state_exists(&grm, &sg.states[usize::from(s7)], "A", 2, 2, vec!["a"]);
        state_exists(&grm, &sg.states[usize::from(s7)], "S", 0, 1, vec!["b", "c"]);

        let s8 = sg.edges[usize::from(s7)][&Symbol::Terminal(grm.terminal_off("c"))];
        assert_eq!(num_active_states(&sg.states[usize::from(s8)]), 1);
        state_exists(&grm, &sg.states[usize::from(s8)], "A", 0, 3, vec!["a"]);

        let s9 = sg.edges[usize::from(s7)][&Symbol::Terminal(grm.terminal_off("b"))];
        assert_eq!(num_active_states(&sg.states[usize::from(s9)]), 2);
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
        let sg = StateGraph::new(&grm);

        assert_eq!(sg.states.len(), 23);
        assert_eq!(sg.edges.iter().fold(0, |a, e| a + e.len()), 27);

        // State 0
        assert_eq!(num_active_states(&sg.states[0]), 7);
        state_exists(&grm, &sg.states[0], "^", 0, 0, vec!["$"]);
        state_exists(&grm, &sg.states[0], "X", 0, 0, vec!["$"]);
        state_exists(&grm, &sg.states[0], "X", 1, 0, vec!["$"]);
        state_exists(&grm, &sg.states[0], "X", 2, 0, vec!["$"]);
        state_exists(&grm, &sg.states[0], "X", 3, 0, vec!["$"]);
        state_exists(&grm, &sg.states[0], "X", 4, 0, vec!["$"]);
        state_exists(&grm, &sg.states[0], "X", 5, 0, vec!["$"]);

        let s1 = sg.edges[0][&Symbol::Terminal(grm.terminal_off("a"))];
        assert_eq!(num_active_states(&sg.states[usize::from(s1)]), 7);
        state_exists(&grm, &sg.states[usize::from(s1)], "X", 0, 1, vec!["a", "d", "e", "$"]);
        state_exists(&grm, &sg.states[usize::from(s1)], "X", 1, 1, vec!["a", "d", "e", "$"]);
        state_exists(&grm, &sg.states[usize::from(s1)], "X", 2, 1, vec!["a", "d", "e", "$"]);
        state_exists(&grm, &sg.states[usize::from(s1)], "Y", 0, 0, vec!["d"]);
        state_exists(&grm, &sg.states[usize::from(s1)], "Y", 1, 0, vec!["d"]);
        state_exists(&grm, &sg.states[usize::from(s1)], "Z", 0, 0, vec!["c"]);
        state_exists(&grm, &sg.states[usize::from(s1)], "T", 0, 0, vec!["a", "d", "e", "$"]);

        let s7 = sg.edges[0][&Symbol::Terminal(grm.terminal_off("b"))];
        assert_eq!(num_active_states(&sg.states[usize::from(s7)]), 7);
        state_exists(&grm, &sg.states[usize::from(s7)], "X", 3, 1, vec!["a", "d", "e", "$"]);
        state_exists(&grm, &sg.states[usize::from(s7)], "X", 4, 1, vec!["a", "d", "e", "$"]);
        state_exists(&grm, &sg.states[usize::from(s7)], "X", 5, 1, vec!["a", "d", "e", "$"]);
        state_exists(&grm, &sg.states[usize::from(s1)], "Y", 0, 0, vec!["d"]);
        state_exists(&grm, &sg.states[usize::from(s1)], "Y", 1, 0, vec!["d"]);
        state_exists(&grm, &sg.states[usize::from(s1)], "Z", 0, 0, vec!["c"]);
        state_exists(&grm, &sg.states[usize::from(s1)], "T", 0, 0, vec!["a", "d", "e", "$"]);

        let s4 = sg.edges[usize::from(s1)][&Symbol::Terminal(grm.terminal_off("u"))];
        assert_eq!(num_active_states(&sg.states[usize::from(s4)]), 8);
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
        assert_eq!(num_active_states(&sg.states[usize::from(s2)]), 3);
        state_exists(&grm, &sg.states[usize::from(s2)], "Y", 0, 1, vec!["d"]);
        state_exists(&grm, &sg.states[usize::from(s2)], "Z", 0, 1, vec!["c"]);
        state_exists(&grm, &sg.states[usize::from(s2)], "W", 0, 0, vec!["d"]);

        let s3 = sg.edges[usize::from(s2)][&Symbol::Terminal(grm.terminal_off("u"))];
        assert_eq!(num_active_states(&sg.states[usize::from(s3)]), 3);
        state_exists(&grm, &sg.states[usize::from(s3)], "Z", 0, 2, vec!["c"]);
        state_exists(&grm, &sg.states[usize::from(s3)], "W", 0, 1, vec!["d"]);
        state_exists(&grm, &sg.states[usize::from(s3)], "V", 0, 0, vec!["d"]);

        let s5 = sg.edges[usize::from(s4)][&Symbol::Nonterminal(grm.nonterminal_off("X"))];
        assert_eq!(num_active_states(&sg.states[usize::from(s5)]), 2);
        state_exists(&grm, &sg.states[usize::from(s5)], "Y", 1, 2, vec!["d", "e"]);
        state_exists(&grm, &sg.states[usize::from(s5)], "T", 0, 2, vec!["a", "d", "e", "$"]);

        let s6 = sg.edges[usize::from(s5)][&Symbol::Terminal(grm.terminal_off("a"))];
        assert_eq!(num_active_states(&sg.states[usize::from(s6)]), 1);
        state_exists(&grm, &sg.states[usize::from(s6)], "T", 0, 3, vec!["a", "d", "e", "$"]);

        let s8 = sg.edges[usize::from(s7)][&Symbol::Terminal(grm.terminal_off("t"))];
        assert_eq!(num_active_states(&sg.states[usize::from(s8)]), 3);
        state_exists(&grm, &sg.states[usize::from(s8)], "Y", 0, 1, vec!["e"]);
        state_exists(&grm, &sg.states[usize::from(s8)], "Z", 0, 1, vec!["d"]);
        state_exists(&grm, &sg.states[usize::from(s8)], "W", 0, 0, vec!["e"]);

        let s9 = sg.edges[usize::from(s8)][&Symbol::Terminal(grm.terminal_off("u"))];
        assert_eq!(num_active_states(&sg.states[usize::from(s9)]), 3);
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
