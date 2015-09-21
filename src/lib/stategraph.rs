use std::collections::HashSet;
use std::collections::hash_map::{Entry, HashMap};

extern crate bit_vec;
use self::bit_vec::BitVec;

use grammar::{AIdx, Grammar, NIdx, Symbol, SIdx, TIdx};

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
/// let grm = ast_to_grammar(parse_yacc(&input));
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
    alt_firsts: Vec<Ctx>,
    alt_epsilons: BitVec,
    terms_len: NIdx
}

impl Firsts {
    /// Generates and returns the firsts set for the given grammar.
    fn new(grm: &Grammar) -> Firsts {
        let mut alt_firsts = Vec::with_capacity(grm.nonterms_len);
        for _ in 0..grm.nonterms_len {
            alt_firsts.push(BitVec::from_elem(grm.terms_len, false));
        }
        let mut firsts = Firsts {
            alt_firsts  : alt_firsts,
            alt_epsilons: BitVec::from_elem(grm.nonterms_len, false),
            terms_len   : grm.terms_len
        };

        // Loop looking for changes to the firsts set, until we reach a fixed point. In essence, we
        // look at each rule E, and see if any of the nonterminals at the start of its alternatives
        // have new elements in since we last looked. If they do, we'll have to do another round.
        loop {
            let mut changed = false;
            for (rul_i, alts) in grm.rules_alts.iter().enumerate() {
                // For each rule E
                for alt_i in alts.iter() {
                    // ...and each alternative A
                    let ref alt = grm.alts[*alt_i];
                    if alt.len() == 0 {
                        // if it's an empty alternative, ensure this nonterminal's epsilon bit is
                        // set.
                        if !firsts.is_epsilon_set(rul_i) {
                            firsts.alt_epsilons.set(rul_i, true);
                            changed = true;
                        }
                        continue;
                    }
                    for (sym_i, sym) in alt.iter().enumerate() {
                        match sym {
                            &Symbol::Terminal(term_i) => {
                                // if symbol is a Terminal, add to FIRSTS
                                if !firsts.set(rul_i, term_i) {
                                    changed = true;
                                }
                                break;
                            },
                            &Symbol::Nonterminal(nonterm_i) => {
                                // if we're dealing with another Nonterminal, union its FIRSTs
                                // together with the current nonterminals FIRSTs. Note this is
                                // (intentionally) a no-op if the two terminals are one and the
                                // same.
                                for bit_i in 0..grm.terms_len {
                                    if firsts.is_set(nonterm_i, bit_i)
                                      && !firsts.set(rul_i, bit_i) {
                                        changed = true;
                                    }
                                }

                                // If the epsilon bit in the nonterminal being referenced is set,
                                // and if its the last symbol in the alternative, then add epsilon
                                // to FIRSTs.
                                if firsts.is_epsilon_set(nonterm_i) && sym_i == alt.len() - 1 {
                                    // Only add epsilon if the symbol is the last in the production
                                    if !firsts.alt_epsilons[rul_i] {
                                        firsts.alt_epsilons.set(rul_i, true);
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
    fn is_set(&self, nidx: NIdx, tidx: TIdx) -> bool {
        self.alt_firsts[nidx][tidx]
    }

    /// Get all the firsts for alternative `nidx` as a `Ctx`.
    fn alt_firsts(&self, nidx: NIdx) -> &Ctx {
        &self.alt_firsts[nidx]
    }

    /// Returns true if the nonterminal `nidx` has epsilon in its first set.
    fn is_epsilon_set(&self, nidx: NIdx) -> bool {
        self.alt_epsilons[nidx]
    }

    /// Ensures that the firsts bit for terminal `tidx` nonterminal `nidx` is set. Returns true if
    /// it was already set, or false otherwise.
    fn set(&mut self, nidx: NIdx, tidx: TIdx) -> bool {
        let mut alt = &mut self.alt_firsts[nidx];
        if alt[tidx] {
            true
        }
        else {
            alt.set(tidx, true);
            false
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Itemset {
    pub items: HashMap<(AIdx, SIdx), Ctx>
}

impl Itemset {
    /// Create a blank Itemset.
    fn new(_: &Grammar) -> Itemset {
        Itemset {items: HashMap::new()}
    }

    /// Add an item `(alt, dot)` with context `ctx` to this itemset. Returns true if this led to
    /// any changes in the itemset.
    fn add(&mut self, alt: AIdx, dot: SIdx, ctx: &Ctx) -> bool {
        let entry = self.items.entry((alt, dot));
        match entry {
            Entry::Occupied(mut e) => {
                e.get_mut().union(&ctx)
            }
            Entry::Vacant(e)       => {
                e.insert(ctx.clone());
                true
            }
        }
    }

    fn close(&self, grm: &Grammar, firsts: &Firsts) -> Itemset {
        // This function can be seen as a merger of getClosure and getContext from Chen's
        // dissertation. It is written in such a style that it allocates relatively little memory
        // and does as few hashmap lookups as practical.

        let mut new_is = self.clone();
        // todo is a list of all (alternative, dot) pairs that require investigation. Not all of
        // these will lead to new entries being put into new_is, but we have to least check them.
        let mut todo = HashSet::new();
        // Seed todo with every (alternative, dot) combination from self.items.
        for &(alt_i, dot) in self.items.keys() {
            todo.insert((alt_i, dot));
        }
        let mut new_ctx = BitVec::from_elem(grm.terms_len, false);
        while todo.len() > 0 {
            // XXX This is the clumsy way we're forced to do what we'd prefer to be:
            //     "let &(alt_i, dot) = todo.pop()"
            let &(alt_i, dot) = todo.iter().next().unwrap();
            todo.remove(&(alt_i, dot));

            let alt = &grm.alts[alt_i];
            if dot == alt.len() { continue; }
            if let Symbol::Nonterminal(nonterm_i) = alt[dot] {
                // This if statement is, in essence, a fast version of what's called getContext in
                // Chen's dissertation, folding in getTHeads at the same time. The particular
                // formulation here is based as much on
                // http://binarysculpting.com/2012/02/04/computing-lr1-closure/ as it is any of the
                // several versions of getTHeads in Chen's dissertation. Nevertheless, the mapping
                // between the two different formulations is fairly straight-forward.
                new_ctx.clear();
                let mut nullable = true;
                for sym in alt.iter().skip(dot + 1) {
                    match sym {
                        &Symbol::Terminal(term_j) => {
                            new_ctx.set(term_j, true);
                            nullable = false;
                            break;
                        },
                        &Symbol::Nonterminal(nonterm_j) => {
                            new_ctx.union(firsts.alt_firsts(nonterm_j));
                            if !firsts.is_epsilon_set(nonterm_j) {
                                nullable = false;
                                break;
                            }
                        }
                    }
                }
                if nullable {
                    new_ctx.union(&new_is.items[&(alt_i, dot)]);
                }

                for ref_alt_i in grm.rules_alts[nonterm_i].iter() {
                    if new_is.add(*ref_alt_i, 0, &new_ctx) {
                        todo.insert((*ref_alt_i, 0));
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
        let mut newis = Itemset::new(&grm);
        for (&(alt_i, dot), ctx) in self.items.iter() {
            let alt = &grm.alts[alt_i];
            if dot == alt.len() { continue; }
            if sym == &alt[dot] {
                newis.add(alt_i, dot + 1, &ctx);
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
        for &(alt_i, dot) in self.items.keys() {
            if other.items.get(&(alt_i, dot)).is_none() {
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
        for i in 0..len - 1 {
            let i_key = keys[i];
            for j in i + 1..len {
                let j_key = keys[j];
                 // Condition 1 in the Pager paper
                if !(bitvec_intersect(&self.items[i_key], &other.items[j_key])
                    || bitvec_intersect(&self.items[j_key], &other.items[i_key])) {
                    continue;
                }
                // Conditions 2 and 3 in the Pager paper
                if bitvec_intersect(&self.items[i_key], &self.items[j_key])
                   || bitvec_intersect(&other.items[i_key], &other.items[j_key]) {
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
        for (&(alt_i, dot), ctx) in self.items.iter_mut() {
            if ctx.union(&other.items[&(alt_i, dot)]) {
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
    pub states: Vec<Itemset>,
    pub edges: HashMap<(usize, Symbol), usize>
}

impl StateGraph {
    /// Create a StateGraph from 'grm'.
    pub fn new(grm: &Grammar) -> StateGraph {
        // This function can be seen as a modified version of items() from Chen's dissertation.

        let firsts     = Firsts::new(grm);
        let mut states = Vec::new();
        let mut edges  = HashMap::new();

        let mut state0 = Itemset::new(&grm);
        let mut ctx = BitVec::from_elem(grm.terms_len, false);
        ctx.set(grm.end_term, true);
        state0.add(grm.start_alt, 0, &ctx);
        states.push(state0);

        // We maintain two lists of which nonterms and terms we've seen; when processing a given
        // state there's no point processing a nonterm or term more than once.
        let mut seen_nonterms = BitVec::from_elem(grm.nonterms_len, false);
        let mut seen_terms = BitVec::from_elem(grm.terms_len, false);
        // new_states is used to separate out iterating over states vs. mutating it
        let mut new_states = Vec::new();
        // todo is a set of integers, representing states which need to be (re)visited
        let mut todo = HashSet::new();
        // cnd_[nonterm|term]_weaklies represent which states are possible weakly compatible
        // matches for a given symbol.
        let mut cnd_nonterm_weaklies: Vec<Vec<usize>> = Vec::with_capacity(grm.nonterms_len);
        let mut cnd_term_weaklies: Vec<Vec<usize>> = Vec::with_capacity(grm.terms_len);
        for _ in 0..grm.terms_len { cnd_term_weaklies.push(Vec::new()); }
        for _ in 0..grm.nonterms_len { cnd_nonterm_weaklies.push(Vec::new()); }

        todo.insert(0);
        while todo.len() > 0 {
            // XXX This is the clumsy way we're forced to do what we'd prefer to be:
            //     "let &(alt_i, dot) = todo.pop()"
            let state_i = *todo.iter().next().unwrap();
            todo.remove(&state_i);

            {
                let state_rc = &states[state_i];
                let state = state_rc.close(&grm, &firsts);
                seen_nonterms.clear();
                seen_terms.clear();
                for &(alt_i, dot) in state.items.keys() {
                    let alt = &grm.alts[alt_i];
                    if dot == alt.len() { continue; }
                    let sym = alt[dot];
                    match sym {
                        Symbol::Nonterminal(nonterm_i) => {
                            if seen_nonterms[nonterm_i] {
                                continue;
                            }
                            seen_nonterms.set(nonterm_i, true);
                        },
                        Symbol::Terminal(term_i) => {
                            if seen_terms[term_i] {
                                continue;
                            }
                            seen_terms.set(term_i, true);
                        }
                    }
                    let nstate = state.goto(&grm, &sym);
                    new_states.push((sym, nstate));
                }
            }

            for (sym, nstate) in new_states.drain(..) {
                let mut m = None;
                {
                    // Try and find a weakly compatible match for this state.
                    let cnd_weaklies = match sym {
                        Symbol::Nonterminal(nonterm_i) => &cnd_nonterm_weaklies[nonterm_i],
                        Symbol::Terminal(term_i) => &cnd_term_weaklies[term_i]
                    };
                    for cnd in cnd_weaklies.iter() {
                        if states[*cnd].weakly_compatible(&nstate) {
                            m = Some(*cnd);
                            break;
                        }
                    }
                }
                match m {
                    Some(k) => {
                        // A weakly compatible match has been found.
                        if let Some(l) = edges.get(&(state_i, sym)) {
                            if k != *l {
                                // My understanding of Pager's algorithm is that reevaluating a
                                // state may cause the outgoing edge for a given symbol to change
                                // from an old state to a new state. If that happens, we would need
                                // to garbage collect states to remove duds. I haven't yet seen a
                                // case where this happens though.
                                panic!("Internal error: states may need garbage collecting");
                            }
                        }
                        edges.insert((state_i, sym), k);
                        if states[k].weakly_merge(&nstate) {
                            todo.insert(k);
                        }
                    },
                    None    => {
                        match sym {
                            Symbol::Nonterminal(nonterm_i) =>
                                cnd_nonterm_weaklies[nonterm_i].push(states.len()),
                            Symbol::Terminal(term_i) =>
                                cnd_term_weaklies[term_i].push(states.len()),
                        }
                        edges.insert((state_i, sym), states.len());
                        // We only do the simplest change propagation, forcing possibly affected
                        // sets to be entirely reprocessed (which will recursively force
                        // propagation too).  Even though this does unnecessary computation, it is
                        // still pretty fast.
                        todo.insert(states.len());
                        states.push(nstate);
                    }
                }
            }
        }

        StateGraph {
            states: states.iter().map(|x| x.close(&grm, &firsts)).collect(),
            edges: edges
        }
    }
}

#[cfg(test)]
mod test {
    extern crate bit_vec;
    use self::bit_vec::BitVec;

    use super::{bitvec_intersect, Itemset, Firsts, StateGraph};
    use grammar::{AIdx, ast_to_grammar, Grammar, Symbol};
    use yacc::parse_yacc;

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
        for (i, n) in grm.terminal_names.iter().enumerate() {
            match should_be.iter().position(|x| x == n) {
                Some(_) => {
                    if !firsts.is_set(nt_i, i) {
                        panic!("{} is not set in {}", n, rn);
                    }
                }
                None    => {
                    if firsts.is_set(nt_i, i) {
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
        let grm = ast_to_grammar(&ast);
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
        let grm = ast_to_grammar(&ast);
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
        let grm = ast_to_grammar(&ast);
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
        let grm = ast_to_grammar(&ast);
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
        let grm = ast_to_grammar(&ast);
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
        ast_to_grammar(&ast)
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
        let grm = ast_to_grammar(&ast);
        let firsts = Firsts::new(&grm);
        has(&grm, &firsts, "E", vec!["a"]);
        has(&grm, &firsts, "T", vec!["a"]);
        has(&grm, &firsts, "P", vec!["a"]);
        has(&grm, &firsts, "C", vec!["c", ""]);
        has(&grm, &firsts, "D", vec!["f", "d", ""]);
        has(&grm, &firsts, "G", vec!["c", "d", "f", ""]);
    }

    fn state_exists(grm: &Grammar, is: &Itemset, nt: &str, alt_off: AIdx, dot: usize, la:
                        Vec<&str>) {
        let ab_alt_off = grm.rules_alts[grm.nonterminal_off(nt)][alt_off];
        let ctx = &is.items[&(ab_alt_off, dot)];
        for i in 0..grm.terms_len {
            let bit = ctx[i];
            let mut found = false;
            for t in la.iter() {
                if grm.terminal_off(t) == i {
                    if !bit {
                        panic!("bit for terminal {}, dot {} is not set in alternative {} of {} when it should be",
                               t, dot, alt_off, nt);
                    }
                    found = true;
                    break;
                }
            }
            if !found && bit {
                panic!("bit for terminal {}, dot {} is set in alternative {} of {} when it shouldn't be",
                       grm.terminal_names[i], dot, alt_off, nt);
            }
        }
    }

    fn num_active_states(is: &Itemset) -> usize {
        is.items.len()
    }


    #[test]
    fn test_dragon_grammar() {
        // From http://binarysculpting.com/2012/02/04/computing-lr1-closure/
        let grm = ast_to_grammar(&parse_yacc(&"
          %start S
          %%
          S: L '=' R | R;
          L: '*' R | 'id';
          R: L;
          ".to_string()).unwrap());
        let firsts = Firsts::new(&grm);

        let mut is = Itemset::new(&grm);
        let mut la = BitVec::from_elem(grm.terms_len, false);
        la.set(grm.terminal_off("$"), true);
        is.add(grm.rules_alts[grm.nonterminal_off("^") as usize][0], 0, &la);
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
        la.set(grm.terminal_off("$"), true);
        is.add(grm.rules_alts[grm.nonterminal_off("^") as usize][0], 0, &la);
        let mut cls_is = is.close(&grm, &firsts);

        state_exists(&grm, &cls_is, "^", 0, 0, vec!["$"]);
        state_exists(&grm, &cls_is, "S", 0, 0, vec!["b", "$"]);
        state_exists(&grm, &cls_is, "S", 1, 0, vec!["b", "$"]);
        state_exists(&grm, &cls_is, "S", 2, 0, vec!["b", "$"]);

        is = Itemset::new(&grm);
        is.add(grm.rules_alts[grm.nonterminal_off("F") as usize][0], 0, &la);
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
        ast_to_grammar(&parse_yacc(&"
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
        la.set(grm.terminal_off("$"), true);
        is.add(grm.rules_alts[grm.nonterminal_off("^") as usize][0], 0, &la);
        let mut cls_is = is.close(&grm, &firsts);

        state_exists(&grm, &cls_is, "^", 0, 0, vec!["$"]);
        state_exists(&grm, &cls_is, "S", 0, 0, vec!["b", "$"]);
        state_exists(&grm, &cls_is, "S", 1, 0, vec!["b", "$"]);

        is = Itemset::new(&grm);
        la = BitVec::from_elem(grm.terms_len, false);
        la.set(grm.terminal_off("b"), true);
        la.set(grm.terminal_off("$"), true);
        is.add(grm.rules_alts[grm.nonterminal_off("S") as usize][1], 1, &la);
        cls_is = is.close(&grm, &firsts);
        state_exists(&grm, &cls_is, "A", 0, 0, vec!["a"]);
        state_exists(&grm, &cls_is, "A", 1, 0, vec!["a"]);
        state_exists(&grm, &cls_is, "A", 2, 0, vec!["a"]);

        is = Itemset::new(&grm);
        la = BitVec::from_elem(grm.terms_len, false);
        la.set(grm.terminal_off("a"), true);
        is.add(grm.rules_alts[grm.nonterminal_off("A") as usize][0], 1, &la);
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
        la.set(grm.terminal_off("$"), true);
        is.add(grm.rules_alts[grm.nonterminal_off("^") as usize][0], 0, &la);
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
        for st in sg.states.iter() { println!("  {:?}", st); }

        assert_eq!(sg.states.len(), 10);
        assert_eq!(sg.edges.len(), 10);

        assert_eq!(num_active_states(&sg.states[0]), 3);
        state_exists(&grm, &sg.states[0], "^", 0, 0, vec!["$"]);
        state_exists(&grm, &sg.states[0], "S", 0, 0, vec!["$", "b"]);
        state_exists(&grm, &sg.states[0], "S", 1, 0, vec!["$", "b"]);

        let s1 = sg.edges[&(0, Symbol::Nonterminal(grm.nonterminal_off("S")))];
        assert_eq!(num_active_states(&sg.states[s1]), 2);
        state_exists(&grm, &sg.states[s1], "^", 0, 1, vec!["$"]);
        state_exists(&grm, &sg.states[s1], "S", 0, 1, vec!["$", "b"]);

        let s2 = sg.edges[&(s1, Symbol::Terminal(grm.terminal_off("b")))];
        assert_eq!(num_active_states(&sg.states[s2]), 1);
        state_exists(&grm, &sg.states[s2], "S", 0, 2, vec!["$", "b"]);

        let s3 = sg.edges[&(0, Symbol::Terminal(grm.terminal_off("b")))];
        assert_eq!(num_active_states(&sg.states[s3]), 4);
        state_exists(&grm, &sg.states[s3], "S", 1, 1, vec!["$", "b", "c"]);
        state_exists(&grm, &sg.states[s3], "A", 0, 0, vec!["a"]);
        state_exists(&grm, &sg.states[s3], "A", 1, 0, vec!["a"]);
        state_exists(&grm, &sg.states[s3], "A", 2, 0, vec!["a"]);

        let s4 = sg.edges[&(s3, Symbol::Nonterminal(grm.nonterminal_off("A")))];
        assert_eq!(num_active_states(&sg.states[s4]), 1);
        state_exists(&grm, &sg.states[s4], "S", 1, 2, vec!["$", "b", "c"]);

        let s5 = sg.edges[&(s4, Symbol::Terminal(grm.terminal_off("a")))];
        assert_eq!(num_active_states(&sg.states[s5]), 1);
        state_exists(&grm, &sg.states[s5], "S", 1, 3, vec!["$", "b", "c"]);

        let s6 = sg.edges[&(s3, Symbol::Terminal(grm.terminal_off("a")))];
        assert_eq!(s3, sg.edges[&(s6, Symbol::Terminal(grm.terminal_off("b")))]); // result from merging 10 into 3
        assert_eq!(num_active_states(&sg.states[s6]), 5);
        state_exists(&grm, &sg.states[s6], "A", 0, 1, vec!["a"]);
        state_exists(&grm, &sg.states[s6], "A", 1, 1, vec!["a"]);
        state_exists(&grm, &sg.states[s6], "A", 2, 1, vec!["a"]);
        state_exists(&grm, &sg.states[s6], "S", 0, 0, vec!["b", "c"]);
        state_exists(&grm, &sg.states[s6], "S", 1, 0, vec!["b", "c"]);

        let s7 = sg.edges[&(s6, Symbol::Nonterminal(grm.nonterminal_off("S")))];
        assert_eq!(num_active_states(&sg.states[s7]), 3);
        state_exists(&grm, &sg.states[s7], "A", 0, 2, vec!["a"]);
        state_exists(&grm, &sg.states[s7], "A", 2, 2, vec!["a"]);
        state_exists(&grm, &sg.states[s7], "S", 0, 1, vec!["b", "c"]);

        let s8 = sg.edges[&(s7, Symbol::Terminal(grm.terminal_off("c")))];
        assert_eq!(num_active_states(&sg.states[s8]), 1);
        state_exists(&grm, &sg.states[s8], "A", 0, 3, vec!["a"]);

        let s9 = sg.edges[&(s7, Symbol::Terminal(grm.terminal_off("b")))];
        assert_eq!(num_active_states(&sg.states[s9]), 2);
        state_exists(&grm, &sg.states[s9], "A", 2, 3, vec!["a"]);
        state_exists(&grm, &sg.states[s9], "S", 0, 2, vec!["b", "c"]);
    }

    // Pager grammar
    fn grammar_pager() -> Grammar {
        ast_to_grammar(&parse_yacc(&"
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

    #[test]
    fn test_pager_graph() {
        let grm = grammar_pager();
        let sg = StateGraph::new(&grm);

        assert_eq!(sg.states.len(), 23);
        assert_eq!(sg.edges.len(), 27);

        // State 0
        assert_eq!(num_active_states(&sg.states[0]), 7);
        state_exists(&grm, &sg.states[0], "^", 0, 0, vec!["$"]);
        state_exists(&grm, &sg.states[0], "X", 0, 0, vec!["$"]);
        state_exists(&grm, &sg.states[0], "X", 1, 0, vec!["$"]);
        state_exists(&grm, &sg.states[0], "X", 2, 0, vec!["$"]);
        state_exists(&grm, &sg.states[0], "X", 3, 0, vec!["$"]);
        state_exists(&grm, &sg.states[0], "X", 4, 0, vec!["$"]);
        state_exists(&grm, &sg.states[0], "X", 5, 0, vec!["$"]);

        let s1 = sg.edges[&(0, Symbol::Terminal(grm.terminal_off("a")))];
        assert_eq!(num_active_states(&sg.states[s1]), 7);
        state_exists(&grm, &sg.states[s1], "X", 0, 1, vec!["a", "d", "e", "$"]);
        state_exists(&grm, &sg.states[s1], "X", 1, 1, vec!["a", "d", "e", "$"]);
        state_exists(&grm, &sg.states[s1], "X", 2, 1, vec!["a", "d", "e", "$"]);
        state_exists(&grm, &sg.states[s1], "Y", 0, 0, vec!["d"]);
        state_exists(&grm, &sg.states[s1], "Y", 1, 0, vec!["d"]);
        state_exists(&grm, &sg.states[s1], "Z", 0, 0, vec!["c"]);
        state_exists(&grm, &sg.states[s1], "T", 0, 0, vec!["a", "d", "e", "$"]);

        let s7 = sg.edges[&(0, Symbol::Terminal(grm.terminal_off("b")))];
        assert_eq!(num_active_states(&sg.states[s7]), 7);
        state_exists(&grm, &sg.states[s7], "X", 3, 1, vec!["a", "d", "e", "$"]);
        state_exists(&grm, &sg.states[s7], "X", 4, 1, vec!["a", "d", "e", "$"]);
        state_exists(&grm, &sg.states[s7], "X", 5, 1, vec!["a", "d", "e", "$"]);
        state_exists(&grm, &sg.states[s1], "Y", 0, 0, vec!["d"]);
        state_exists(&grm, &sg.states[s1], "Y", 1, 0, vec!["d"]);
        state_exists(&grm, &sg.states[s1], "Z", 0, 0, vec!["c"]);
        state_exists(&grm, &sg.states[s1], "T", 0, 0, vec!["a", "d", "e", "$"]);

        let s4 = sg.edges[&(s1, Symbol::Terminal(grm.terminal_off("u")))];
        assert_eq!(num_active_states(&sg.states[s4]), 8);
        assert_eq!(s4, sg.edges[&(s7, Symbol::Terminal(grm.terminal_off("u")))]);
        state_exists(&grm, &sg.states[s4], "Y", 1, 1, vec!["d", "e"]);
        state_exists(&grm, &sg.states[s4], "T", 0, 1, vec!["a", "d", "e", "$"]);
        state_exists(&grm, &sg.states[s4], "X", 0, 0, vec!["a", "d", "e"]);
        state_exists(&grm, &sg.states[s4], "X", 1, 0, vec!["a", "d", "e"]);
        state_exists(&grm, &sg.states[s4], "X", 2, 0, vec!["a", "d", "e"]);
        state_exists(&grm, &sg.states[s4], "X", 3, 0, vec!["a", "d", "e"]);
        state_exists(&grm, &sg.states[s4], "X", 4, 0, vec!["a", "d", "e"]);
        state_exists(&grm, &sg.states[s4], "X", 5, 0, vec!["a", "d", "e"]);

        assert_eq!(s1, sg.edges[&(s4, Symbol::Terminal(grm.terminal_off("a")))]);
        assert_eq!(s7, sg.edges[&(s4, Symbol::Terminal(grm.terminal_off("b")))]);

        let s2 = sg.edges[&(s1, Symbol::Terminal(grm.terminal_off("t")))];
        assert_eq!(num_active_states(&sg.states[s2]), 3);
        state_exists(&grm, &sg.states[s2], "Y", 0, 1, vec!["d"]);
        state_exists(&grm, &sg.states[s2], "Z", 0, 1, vec!["c"]);
        state_exists(&grm, &sg.states[s2], "W", 0, 0, vec!["d"]);

        let s3 = sg.edges[&(s2, Symbol::Terminal(grm.terminal_off("u")))];
        assert_eq!(num_active_states(&sg.states[s3]), 3);
        state_exists(&grm, &sg.states[s3], "Z", 0, 2, vec!["c"]);
        state_exists(&grm, &sg.states[s3], "W", 0, 1, vec!["d"]);
        state_exists(&grm, &sg.states[s3], "V", 0, 0, vec!["d"]);

        let s5 = sg.edges[&(s4, Symbol::Nonterminal(grm.nonterminal_off("X")))];
        assert_eq!(num_active_states(&sg.states[s5]), 2);
        state_exists(&grm, &sg.states[s5], "Y", 1, 2, vec!["d", "e"]);
        state_exists(&grm, &sg.states[s5], "T", 0, 2, vec!["a", "d", "e", "$"]);

        let s6 = sg.edges[&(s5, Symbol::Terminal(grm.terminal_off("a")))];
        assert_eq!(num_active_states(&sg.states[s6]), 1);
        state_exists(&grm, &sg.states[s6], "T", 0, 3, vec!["a", "d", "e", "$"]);

        let s8 = sg.edges[&(s7, Symbol::Terminal(grm.terminal_off("t")))];
        assert_eq!(num_active_states(&sg.states[s8]), 3);
        state_exists(&grm, &sg.states[s8], "Y", 0, 1, vec!["e"]);
        state_exists(&grm, &sg.states[s8], "Z", 0, 1, vec!["d"]);
        state_exists(&grm, &sg.states[s8], "W", 0, 0, vec!["e"]);

        let s9 = sg.edges[&(s8, Symbol::Terminal(grm.terminal_off("u")))];
        assert_eq!(num_active_states(&sg.states[s9]), 3);
        state_exists(&grm, &sg.states[s9], "Z", 0, 2, vec!["d"]);
        state_exists(&grm, &sg.states[s9], "W", 0, 1, vec!["e"]);
        state_exists(&grm, &sg.states[s3], "V", 0, 0, vec!["d"]);

        // Ommitted successors from the graph in Fig.3

        // X-successor of S0
        let s0x = sg.edges[&(0, Symbol::Nonterminal(grm.nonterminal_off("X")))];
        state_exists(&grm, &sg.states[s0x], "^", 0, 1, vec!["$"]);

        // Y-successor of S1 (and it's d-successor)
        let s1y = sg.edges[&(s1, Symbol::Nonterminal(grm.nonterminal_off("Y")))];
        state_exists(&grm, &sg.states[s1y], "X", 0, 2, vec!["a", "d", "e", "$"]);
        let s1yd = sg.edges[&(s1y, Symbol::Terminal(grm.terminal_off("d")))];
        state_exists(&grm, &sg.states[s1yd], "X", 0, 3, vec!["a", "d", "e", "$"]);

        // Z-successor of S1 (and it's successor)
        let s1z = sg.edges[&(s1, Symbol::Nonterminal(grm.nonterminal_off("Z")))];
        state_exists(&grm, &sg.states[s1z], "X", 1, 2, vec!["a", "d", "e", "$"]);
        let s1zc = sg.edges[&(s1z, Symbol::Terminal(grm.terminal_off("c")))];
        state_exists(&grm, &sg.states[s1zc], "X", 1, 3, vec!["a", "d", "e", "$"]);

        // T-successor of S1
        let s1t = sg.edges[&(s1, Symbol::Nonterminal(grm.nonterminal_off("T")))];
        state_exists(&grm, &sg.states[s1t], "X", 2, 2, vec!["a", "d", "e", "$"]);

        // Y-successor of S7 (and it's d-successor)
        let s7y = sg.edges[&(s7, Symbol::Nonterminal(grm.nonterminal_off("Y")))];
        state_exists(&grm, &sg.states[s7y], "X", 3, 2, vec!["a", "d", "e", "$"]);
        let s7ye = sg.edges[&(s7y, Symbol::Terminal(grm.terminal_off("e")))];
        state_exists(&grm, &sg.states[s7ye], "X", 3, 3, vec!["a", "d", "e", "$"]);

        // Z-successor of S7 (and it's successor)
        let s7z = sg.edges[&(s7, Symbol::Nonterminal(grm.nonterminal_off("Z")))];
        state_exists(&grm, &sg.states[s7z], "X", 4, 2, vec!["a", "d", "e", "$"]);
        let s7zd = sg.edges[&(s7z, Symbol::Terminal(grm.terminal_off("d")))];
        state_exists(&grm, &sg.states[s7zd], "X", 4, 3, vec!["a", "d", "e", "$"]);

        // T-successor of S7
        let s7t = sg.edges[&(s7, Symbol::Nonterminal(grm.nonterminal_off("T")))];
        state_exists(&grm, &sg.states[s7t], "X", 5, 2, vec!["a", "d", "e", "$"]);

        // W-successor of S2 and S8 (merged)
        let s8w = sg.edges[&(s8, Symbol::Nonterminal(grm.nonterminal_off("W")))];
        assert_eq!(s8w, sg.edges[&(s2, Symbol::Nonterminal(grm.nonterminal_off("W")))]);
        state_exists(&grm, &sg.states[s8w], "Y", 0, 2, vec!["d", "e"]);

        // V-successor of S3 and S9 (merged)
        let s9v = sg.edges[&(s9, Symbol::Nonterminal(grm.nonterminal_off("V")))];
        assert_eq!(s9v, sg.edges[&(s3, Symbol::Nonterminal(grm.nonterminal_off("V")))]);
        state_exists(&grm, &sg.states[s9v], "W", 0, 2, vec!["d", "e"]);
    }
}
