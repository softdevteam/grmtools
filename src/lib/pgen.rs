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
pub struct Firsts {
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
    pub fn is_set(&self, nidx: NIdx, tidx: TIdx) -> bool {
        self.alt_firsts[nidx][tidx]
    }

    /// Get all the firsts for alternative `nidx` as a `Ctx`.
    pub fn alt_firsts(&self, nidx: NIdx) -> &Ctx {
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

#[derive(Clone, Debug, PartialEq)]
pub struct Itemset {
    pub items: HashMap<(AIdx, SIdx), Ctx>
}

impl Itemset {
    /// Create a blank Itemset.
    pub fn new(_: &Grammar) -> Itemset {
        Itemset {items: HashMap::new()}
    }

    /// Add an item `(alt, dot)` with context `ctx` to this itemset. Returns true if this led to
    /// any changes in the itemset.
    pub fn add(&mut self, alt: AIdx, dot: SIdx, ctx: &Ctx) -> bool {
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

    pub fn close(&self, grm: &Grammar, firsts: &Firsts) -> Itemset {
        // This function can be seen as a merger of getClosure and getContext from Chen's
        // dissertation. It is written in such a style that it allocates relatively little memory
        // and does as few hashmap lookups as practical.

        let mut new_is = self.clone();
        // todo is a list of all (alternative, dot) pairs that require investigation. Not all of
        // these will lead to new entries being put into new_is, but we have to least check them.
        let mut todo = HashSet::new();
        // Seed todo with every (alternative, dot) combination from self.items.
        for (&(alt_i, dot), _) in self.items.iter() {
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
    pub fn goto(&self, grm: &Grammar, sym: &Symbol) -> Itemset {
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
        // states wraps its contents in an Rc<RefCell> because in the loop below we need to have a
        // read of an item within the vector whilst also being able to push extra elements into it.
        let mut states = Vec::new();
        let mut edges  = HashMap::new();

        let mut state0 = Itemset::new(&grm);
        let mut ctx = BitVec::from_elem(grm.terms_len, false);
        ctx.set(grm.end_term, true);
        state0.add(grm.start_alt, 0, &ctx);
        states.push(state0.close(&grm, &firsts));

        let mut seen_nonterms = BitVec::from_elem(grm.nonterms_len, false);
        let mut seen_terms = BitVec::from_elem(grm.terms_len, false);
        let mut state_i = 0; // How far through states have we processed so far?
        let mut new_states = Vec::new();
        while state_i < states.len() {
            {
                let state_rc = &states[state_i];
                let state = state_rc;
                // We maintain two lists of which nonterms and terms we've seen; when processing a
                // given state there's no point processing a nonterm or term more than once.
                seen_nonterms.clear();
                seen_terms.clear();
                for &(alt_i, dot) in state.items.keys() {
                    let alt = &grm.alts[alt_i];
                    if dot == alt.len() { continue; }
                    let sym = alt[dot].clone();
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
                    let nstate = state.goto(&grm, &sym).close(&grm, &firsts);
                    new_states.push((sym, nstate));
                }
            }
            for (sym, nstate) in new_states.drain(..) {
                let j = states.iter().position(|x| x == &nstate);
                match j {
                    Some(k) => { edges.insert((state_i, sym), k); },
                    None    => {
                        edges.insert((state_i, sym), states.len());
                        states.push(nstate);
                    }
                }
            }
            state_i += 1;
        }

        StateGraph {
            states: states,
            edges: edges
        }
    }
}

