use std::collections::HashMap;
use std::cell::RefCell;

extern crate bit_vec;
use self::bit_vec::BitVec;

use grammar::{AIdx, Grammar, NIdx, Symbol, SIdx, TIdx};

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
pub struct Firsts {
    // The representation is a contiguous bitfield, of (terms_len * 1) * nonterms_len. Put another
    // way, each nonterminal has (terms_len + 1) bits, where the bit at position terms_len
    // represents epsilon. So for the grammar given above, the bitvector would be two sequences of
    // 3 bits where bits 0, 1, 2 represent terminals a, b, epsilon respectively.
    //   111101
    // Where "111" is for the nonterminal S, and 101 for A.
    alt_firsts: Vec<BitVec>,
    alt_epsilons: BitVec,
    terms_len: NIdx
}

impl Firsts {
    /// Generates and returns the firsts set for the given grammar.
    pub fn new(grm: &Grammar) -> Firsts {
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
                        // if it's an empty alternative, ensure this nonterminal's epsilon bit is set.
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
    pub fn is_set(&self, nidx: NIdx, tidx: TIdx) -> bool {
        self.alt_firsts[nidx][tidx]
    }

    /// Get all the firsts for alternative `nidx` as a `BitVec`.
    pub fn alt_firsts(&self, nidx: NIdx) -> &BitVec {
        &self.alt_firsts[nidx]
    }

    /// Returns true if the nonterminal `nidx` has epsilon in its first set.
    pub fn is_epsilon_set(&self, nidx: NIdx) -> bool {
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

#[derive(Debug, PartialEq)]
pub struct Itemset {
    // This immutable vector stores a Item for each alternative in the grammar, in the same
    // order as grm.alts.
    pub items: Vec<RefCell<Option<Item>>>
}

// An Item instance represents all the possible items that derive from a given alternative in a
// grammar. We know that if a given alternative E has n symbols, it can lead to at most n+1 items.
// For example, Consider an alternative:
//    E : 'b' S;
// There are at most three possible items that this alternative can lead to:
//    E : . 'b' S;
//    E : 'b' . S;
//    E : 'b' S .;
// Each of these items can then have one or more terminals as lookahead (crucially, each terminal
// can only appear once in the lookahead). Knowing this, we can create a very compact fixed-size
// representation with room for all the possible items that an alternative can lead to.
//
// Let us assume that our state has the following items:
//    E : . 'b' S; // Lookahead 'a' and '$'
//    E : 'b' S .; // Lookahead '$'
// and the terminals '$' (bit 0), 'a' (bit 1), and 'b' (bit 2) only. 'lookaheads' then lookaheads
// would then be set to something along the lines of:
//    [RefCell(Some(BitVec(011))), RefCell(None), RefCell(Some(BitVec(001)))]
// Where "011" corresponds to "E: . 'b' S;", and 001 corresponds to "E: 'b' S .;".
#[derive(Debug, PartialEq)]
pub struct Item {
    pub lookaheads: Vec<RefCell<Option<BitVec>>>
}

impl Itemset {
    /// Create a blank Itemset.
    pub fn new(grm: &Grammar) -> Itemset {
        let mut items = Vec::with_capacity(grm.alts.len());
        for _ in grm.alts.iter() {
            items.push(RefCell::new(None));
        }
        Itemset {items: items}
    }

    /// Ensure that memory is allocated for dot `dot` in alternative `aidx` in itemset `is`.
    ///
    /// If memory is already allocated, this is a no-op. If no memory is yet allocated, it will
    /// allocate it.
    fn ensure_lookahead_allocd(&self, grm: &Grammar, is: &Itemset, aidx: AIdx, dot: SIdx) {
        let mut item_opt = is.items[aidx].borrow_mut();
        if item_opt.is_none() {
            let mut las = Vec::with_capacity(grm.alts[aidx].len());
            for _ in 0..grm.alts[aidx].len() + 1 {
                las.push(RefCell::new(None));
            }
            *item_opt = Some(Item{lookaheads: las});
        }
        let mut la_opt = item_opt.as_ref().unwrap().lookaheads[dot].borrow_mut();
        if la_opt.is_none() {
            *la_opt = Some(BitVec::from_elem(grm.terms_len, false));
        }
    }

    /// Add an item for the alternative 'aidx' with the dot set to position 'dot' and with
    /// lookahead set to 'la'.
    pub fn add(&self, grm: &Grammar, aidx: AIdx, dot: SIdx, la: &BitVec) {
        assert!(la.len() == grm.terms_len);
        self.ensure_lookahead_allocd(&grm, &self, aidx, dot);
        let item_opt = self.items[aidx].borrow_mut();
        let mut la_opt = item_opt.as_ref().unwrap().lookaheads[dot].borrow_mut();
        debug_assert!(la_opt.as_ref().unwrap().none());
        la_opt.as_mut().unwrap().union(la);
    }

    /// Close over this Itemset.
    pub fn close(&self, grm: &Grammar, firsts: &Firsts) {
        let mut new_la = BitVec::from_elem(grm.terms_len, false);
        loop {
            let mut changed = false;
            for (i, item_rc) in self.items.iter().enumerate() {
                if item_rc.borrow().is_none() { continue; }
                let alt = &grm.alts[i];
                for dot in 0..alt.len() {
                    {
                        let item_opt = item_rc.borrow();
                        if item_opt.as_ref().unwrap().lookaheads[dot].borrow().is_none() { continue; }
                    }
                    if let Symbol::Nonterminal(nonterm_i) = alt[dot] {
                        new_la.clear();
                        let mut nullabled = false;
                        for k in dot + 1..alt.len() {
                            match alt[k] {
                                Symbol::Terminal(term_j) => {
                                    new_la.set(term_j, true);
                                    nullabled = true;
                                    break;
                                },
                                Symbol::Nonterminal(nonterm_j) => {
                                    new_la.union(firsts.alt_firsts(nonterm_j));
                                    if !firsts.is_epsilon_set(nonterm_j) {
                                        nullabled = true;
                                        break;
                                    }
                                }
                            }
                        }
                        if !nullabled {
                            let item_opt = item_rc.borrow();
                            let la_opt = item_opt.as_ref().unwrap().lookaheads[dot].borrow();
                            new_la.union(&la_opt.as_ref().unwrap());
                        }

                        for alt_i in grm.rules_alts[nonterm_i].iter() {
                            self.ensure_lookahead_allocd(&grm, &self, *alt_i, 0);
                            let clitem_opt = self.items[*alt_i].borrow_mut();
                            let mut clla_opt = clitem_opt.as_ref().unwrap().lookaheads[0].borrow_mut();
                            if clla_opt.as_mut().unwrap().union(&new_la) { changed = true; }
                        }
                    }
                }
            }
            if !changed { break; }
        }
    }

    /// Create a new Itemset based on calculating goto of 'sym' on the current Itemset.
    pub fn goto(&self, grm: &Grammar, firsts: &Firsts, sym: Symbol) -> Itemset {
        let newis = Itemset::new(&grm);
        {
            let items = &self.items;
            let newitems = &newis.items;
            for (i, item_rc) in items.iter().enumerate() {
                let item_opt = item_rc.borrow();
                if item_opt.is_none() { continue; }
                let lookaheads = &item_opt.as_ref().unwrap().lookaheads;
                let alt = &grm.alts[i];
                for dot in 0..alt.len() {
                    let la_rc = lookaheads[dot].borrow();
                    if la_rc.is_none() { continue; }
                    if sym == alt[dot] {
                        self.ensure_lookahead_allocd(&grm, &newis, i, dot + 1);
                        let newitem_opt = newitems[i].borrow_mut();
                        let mut newla_opt = newitem_opt.as_ref().unwrap().lookaheads[dot + 1].borrow_mut();
                        newla_opt.as_mut().unwrap().union(&la_rc.as_ref().unwrap());
                    }
                }
            }
            newis.close(&grm, &firsts);
        }
        newis
    }
}

pub struct StateGraph {
    pub states: Vec<Itemset>,
    pub edges: HashMap<(usize, Symbol), usize>
}

impl StateGraph {
    /// Create a StateGraph from 'grm'.
    pub fn new(grm: &Grammar) -> StateGraph {
        let firsts     = Firsts::new(grm);
        let mut states = Vec::new();
        let mut edges  = HashMap::new();

        // Create the start state and seed the stategraph with it
        let state0 = Itemset::new(&grm);
        let mut la = BitVec::from_elem(grm.terms_len, false);
        la.set(grm.end_term, true);
        state0.add(&grm, grm.start_alt, 0, &la);
        state0.close(&grm, &firsts);
        states.push(state0);

        let mut seen_nonterms = BitVec::from_elem(grm.nonterms_len, false);
        let mut seen_terms = BitVec::from_elem(grm.terms_len, false);
        let mut state_i = 0; // How far through states have we processed so far?
        while state_i < states.len() {
            // We maintain two lists of which nonterms and terms we've seen; when processing a
            // given state there's no point processing any given nonterm or term more than once.
            seen_nonterms.clear();
            seen_terms.clear();
            // Iterate over active item in the stategraph.
            for i in 0..grm.alts.len() {
                if states[state_i].items[i].borrow().is_none() { continue; }
                // From this point onwards in the for loop, we know that states[state_i].items is
                // definitely allocated and that calling unwrap() on it is safe.
                let alt = &grm.alts[i];
                for dot in 0..alt.len() {
                    let sym;
                    let nstate;
                    {
                        let state = &states[state_i] as &Itemset;
                        let item_opt = state.items[i].borrow();
                        if item_opt.as_ref().unwrap().lookaheads[dot].borrow().is_none() {
                            continue;
                        }
                        // We have an active item. If the symbol at the dot hasn't been seen
                        // before, we calculate its goto relative to the current state. We then add
                        // that new state to the list of states.
                        sym = &alt[dot];
                        match sym {
                            &Symbol::Nonterminal(nonterm_i) => {
                                if seen_nonterms[nonterm_i] {
                                    continue;
                                }
                                seen_nonterms.set(nonterm_i, true);
                            },
                            &Symbol::Terminal(term_i) => {
                                if seen_terms[term_i] {
                                    continue;
                                }
                                seen_terms.set(term_i, true);
                            }
                        }
                        nstate = state.goto(&grm, &firsts, sym.clone());
                    }
                    let j = states.iter().position(|x| x == &nstate);
                    match j {
                        Some(k) => { edges.insert((state_i, sym.clone()), k); },
                        None    => {
                            edges.insert((state_i, sym.clone()), states.len());
                            states.push(nstate);
                        }
                    }
                }
            }
            state_i += 1;
        }
        StateGraph{states: states, edges: edges}
    }
}

