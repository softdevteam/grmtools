use grammar::{Grammar, Symbol, SymbolType};
use std::collections::{HashMap, HashSet};

struct ParserGenerator;

pub fn calc_firsts(grm: Grammar) -> HashMap<String, HashSet<String>> {
    // This function gradually builds up a FIRST hashmap in stages.
    let mut firsts: HashMap<String, HashSet<String>> = HashMap::new();

    // First do the easy bit, which is every terminal at the start of an alternative.
    for rul in grm.rules.values() {
        let mut f = HashSet::new();
        for alt in rul.alternatives.iter() {
            if alt.len() == 0 { continue; }
            let ref sym = alt[0];
            if sym.typ == SymbolType::Terminal {
                f.insert(sym.name.clone());
            }
        }
        firsts.insert(rul.name.clone(), f);
    }

    // Now we do the slow, iterative part, where we loop until we reach a fixed point. In essence,
    // we look at each rule E, and see if any of the nonterminals at the start of its alternatives
    // have new elements in since we last looked. If they do, we'll have to do another round.
    let mut changed;
    loop {
        changed = false;
        for rul in grm.rules.values() {
            // For each rule E...
            for alt in rul.alternatives.iter() {
                // ...and each alternative A
                for sym in alt.iter() {
                    if sym.typ == SymbolType::Terminal { break; }
                    assert!(sym.typ == SymbolType::Nonterminal);
                    // ...and for each nonterminal X at the beginning of A, see if each terminal T
                    // in FIRSTS(X) is in FIRSTS(E). If not, add T to FIRSTS(E) and set the changed
                    // flag, as we need to do another loop.
                    let of = firsts.get(&sym.name).unwrap().clone();
                    let mut f = firsts.get_mut(&rul.name).unwrap();
                    for n in of.iter() {
                        if !f.contains(n) {
                            f.insert(n.clone());
                            changed = true;
                        }
                    }
                }
            }
        }
        if !changed {
            return firsts;
        }
    }
}
