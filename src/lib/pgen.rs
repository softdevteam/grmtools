use std::collections::HashMap;
use std::cell::RefCell;
use std::rc::Rc;

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
    bf: BitVec,
    terms_len: NIdx
}

impl Firsts {
    /// Generates and returns the firsts set for the given grammar.
    pub fn new(grm: &Grammar) -> Firsts {
        let mut firsts = Firsts {
            bf        : BitVec::from_elem((grm.nonterms_len * (grm.terms_len + 1)), false),
            terms_len : grm.terms_len
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
                        if !firsts.set(rul_i, grm.terms_len) {
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
                                    // only add epsilon if the symbol is the last in the production
                                    if !firsts.set(rul_i, grm.terms_len) {
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

    /// Returns true if the terminal `tidx' is in the first set for nonterminal `nidx` is set.
    pub fn is_set(&self, nidx: NIdx, tidx: TIdx) -> bool {
        assert!(tidx < self.terms_len);
        self.bf[nidx * (self.terms_len + 1) + tidx]
    }

    /// Returns true if the nonterminal `nidx' has epsilon in its first set.
    pub fn is_epsilon_set(&self, nidx: NIdx) -> bool {
        self.bf[nidx * (self.terms_len + 1) + self.terms_len]
    }

    /// Ensures that the firsts bit for terminal `tidx` nonterminal `nidx` is set. Returns true if
    /// it was already set, or false otherwise. Bit `terms_len` represents epsilon.
    fn set(&mut self, nidx: NIdx, tidx: TIdx) -> bool {
        let off = nidx * (self.terms_len + 1) + tidx;
        if self.bf[off] {
            true
        }
        else {
            self.bf.set(off, true);
            false
        }
    }
}

#[derive(Debug, PartialEq)]
pub struct Itemset {
    // This immutable vector stores a Item for each alternative in the grammar, in the same
    // order as grm.alts.
    pub items: Rc<Vec<RefCell<Item>>>
}

#[derive(Debug, PartialEq)]
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
// active is a bitfield of length n+1 (where n is the number of symbols in an alternative). If bit
// i is set, it means that there is an item with a dot at position i. When this is set, the
// corresponding section of the dots bitvec is then meaningful.
//
// dots is a bitfield of length (n + 1)*grm.terms_len i.e. for each dot, it stores a single bit for
// each terminal in the grammar. Note that, unlike Firsts::bf, we do not need a bit to represent
// epsilon.
//
// Let us assume that our state has the following items:
//    E : . 'b' S; // Lookahead 'a' and '$'
//    E : 'b' S .; // Lookahead '$'
// then active would be set to:
//   101
// and (assuming the grammar has terminals '$', 'a', and 'b' only) dots would be something like the
// following (depending on the order the terminals are stored in grm.terminal_names):
//   011000001
// Where "011" corresponds to "E: . 'b' S;", the middle 000 are inactive, and 001 corresponds to
// "E: 'b' S .;".
pub struct Item {
    pub active: BitVec,
    pub dots: BitVec
}

impl Itemset {
    /// Create a blank Itemset.
    pub fn new(grm: &Grammar) -> Itemset {
        let mut items = Vec::with_capacity(grm.alts.len());
        for alt in grm.alts.iter() {
            let num_syms = alt.len() + 1;
            items.push(RefCell::new(Item {
                active: BitVec::from_elem(num_syms, false),
                dots  : BitVec::from_elem(grm.terms_len * num_syms, false)
            }));
        }
        Itemset {items: Rc::new(items)}
    }

    /// Add an item for the alternative 'aidx' with the dot set to position 'dot' and with
    /// lookahead set to 'la'.
    pub fn add(&self, grm: &Grammar, aidx: AIdx, dot: SIdx, la: &BitVec) {
        if la.len() != grm.terms_len {
            panic!("Passed a bitfield of length {} instead of {}", la.len(), grm.terms_len);
        }
        let mut alt_cl = self.items[aidx].borrow_mut();
        alt_cl.active.set(dot, true);
        let dots = &mut alt_cl.dots;
        for (i, bit) in la.iter().enumerate() {
            if bit {
                dots.set(dot * grm.nonterms_len + i, true);
            }
        }
    }

    /// Close over this Itemset.
    pub fn close(&self, grm: &Grammar, firsts: &Firsts) {
        let items = &self.items;
        let mut new_la = BitVec::from_elem(grm.terms_len, false);
        loop {
            let mut changed = false;
            for i in 0..items.len() {
                let alt = &grm.alts[i];
                for dot in 0..alt.len() {
                    if !items[i].borrow().active[dot] { continue; }
                    if dot == alt.len() { continue; }
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
                                    for l in 0..grm.terms_len {
                                        if firsts.is_set(nonterm_j, l) {
                                            new_la.set(l, true);
                                        }
                                    }
                                    if !firsts.is_epsilon_set(nonterm_j) {
                                        nullabled = true;
                                        break;
                                    }
                                }
                            }
                        }
                        if !nullabled {
                            let dots = &items[i].borrow().dots;
                            for l in 0..grm.terms_len {
                                if dots[dot * grm.terms_len + l] {
                                    new_la.set(l, true);
                                }
                            }
                        }

                        for alt_i in grm.rules_alts[nonterm_i].iter() {
                            let mut clalt = items[*alt_i].borrow_mut();
                            if !clalt.active[0] {
                                clalt.active.set(0, true);
                                changed = true;
                            }
                            for l in 0..grm.terms_len {
                                if new_la[l] && !clalt.dots[l] {
                                    clalt.dots.set(l, true);
                                    changed = true;
                                }
                            }
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
            for i in 0..items.len() {
                let item = items[i].borrow_mut();
                let mut newitem = newitems[i].borrow_mut();
                let alt = &grm.alts[i];
                for dot in 0..alt.len() {
                    if !item.active[dot] { continue; }
                    if sym == alt[dot] {
                        newitem.active.set(dot + 1, true);
                        for j in 0..grm.terms_len {
                            if item.dots[dot * grm.terms_len + j] {
                                newitem.dots.set((dot + 1) * grm.terms_len + j, true);
                            }
                        }
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
        state0.add(&grm, grm.start_rule, 0, &la);
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
                let alt = &grm.alts[i];
                for dot in 0..alt.len() {
                    let sym;
                    let nstate;
                    {
                        let state = &states[state_i] as &Itemset;
                        if !state.items[i].borrow().active[dot] { continue; }
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

