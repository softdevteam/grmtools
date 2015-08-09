use grammar::{Grammar, Symbol, SymbolType};
use std::collections::{HashMap, HashSet};

struct ParserGenerator;

pub fn calc_firsts(grm: Grammar) -> HashMap<String, HashSet<Symbol>> {
    // This function gradually builds up a FIRST hashmap in stages.
    let mut firsts: HashMap<String, HashSet<Symbol>> = HashMap::new();
    let eps = Symbol::new("".to_string(), SymbolType::Epsilon);

    // First do the easy bit, which is every terminal at the start of an alternative.
    for rul in grm.rules.values() {
        let mut f = HashSet::new();
        for alt in rul.alternatives.iter() {
            if alt.len() == 0 { continue; }
            let ref sym = alt[0];
            if sym.typ == SymbolType::Terminal || sym.typ == SymbolType::Epsilon {
                f.insert(sym.clone());
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
                for (sym_i, sym) in alt.iter().enumerate() {
                    match sym.typ {
                        // epsilon can only appear on their own we already dealt with them earlier
                        SymbolType::Epsilon => break,
                        SymbolType::Terminal => {
                            // if symbol is a Terminal, add to FIRSTS
                            let mut f = firsts.get_mut(&rul.name).unwrap();
                            if !f.contains(sym) {
                                f.insert(sym.clone());
                                changed = true;
                            }
                            break;
                        },
                        SymbolType::Nonterminal => {
                            // if symbols is Nonterminal, get its FIRSTS and add them to the
                            // current FIRSTS. if the Nonterminals FIRSTS contain an epsilon,
                            // continue looking at the succeeding Nonterminal, otherwise break
                            let of = firsts.get(&sym.name).unwrap().clone();
                            let mut f = firsts.get_mut(&rul.name).unwrap();
                            for n in of.iter() {
                                if n.typ == SymbolType::Epsilon {
                                    // only add epsilon if symbol is the last in the production
                                    if sym_i == alt.len() - 1 {
                                        if !f.contains(n) {
                                            f.insert(n.clone());
                                            changed = true;
                                        }
                                    }
                                }
                                else if !f.contains(n) {
                                    f.insert(n.clone());
                                    changed = true;
                                }
                            }
                            // if FIRST(X) of production R : X Y2 Y3 doesn't contain epsilon, don't
                            // add FIRST(Y2 Y3)
                            if !of.contains(&eps) {
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
