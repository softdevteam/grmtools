use grammar::{Grammar, Symbol, SymbolType};
use std::collections::{HashMap, HashSet};

/// Generates and returns the first set for the given grammar.
///
/// # Example
/// Given a grammar `grm`:
///
/// ```c
/// S : A "b";
/// A : "a" |;
/// ```
///
/// ```c
/// let firsts = calc_firsts(&grm);
/// println!(firsts); // {"S": {"a", "b"}, "A": {"a"}};
/// ```
pub fn calc_firsts(grm: &Grammar) -> HashMap<String, HashSet<String>> {
    // This function gradually builds up a FIRST hashmap in stages.
    let mut firsts: HashMap<String, HashSet<String>> = HashMap::new();

    // First do the easy bit, which is every terminal at the start of an alternative.
    for rul in grm.rules.values() {
        let mut f = HashSet::new();
        for alt in rul.alternatives.iter() {
            if alt.len() == 0 { 
                f.insert("".to_string());
                continue;
            }
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
                for (sym_i, sym) in alt.iter().enumerate() {
                    match sym.typ {
                        SymbolType::Terminal => {
                            // if symbol is a Terminal, add to FIRSTS
                            let mut f = firsts.get_mut(&rul.name).unwrap();
                            if !f.contains(&sym.name) {
                                f.insert(sym.name.clone());
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
                                if n == "" {
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
                            if !of.contains("") {
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

/// Returns the first set for the given list of symbols.
///
/// # Example
/// Given a grammar `grm`:
///
/// ```c
/// S : A "b";
/// A : "a" |;
/// ```
///
/// ```c
/// let firsts = calc_firsts(&grm);
/// let symbols = vec![nonterminal!("A"), terminal!("b")];
/// let f = get_firsts_from_symbols(&firsts, &symbols);
/// println!(f); // {"a", "b"};
/// ```
pub fn get_firsts_from_symbols(firsts: &HashMap<String, HashSet<String>>,
                               symbols: &Vec<Symbol>) -> HashSet<String> {
    let mut r = HashSet::new();
    for (i, s) in symbols.iter().enumerate() {
        match s.typ {
            SymbolType::Terminal => {
                r.insert(s.name.clone());
                break;
            },
            SymbolType::Nonterminal => {
                let f = firsts.get(&s.name).unwrap();
                for e in f {
                    if e == "" && i != symbols.len() - 1 {
                        continue;
                    }
                    r.insert(e.clone());
                }
                if f.contains("") {
                    continue;
                }
                break;
            }
        }
    }
    r
}

/// Generates and returns the follow set for the given grammar.
///
/// # Example
/// Given a grammar `grm`:
///
/// ```c
/// S : A "b";
/// A : "a" |;
/// ```
///
/// ```c
/// let firsts = calc_firsts(&grm);
/// let follows = calc_follows(&grm, &firsts);
/// println!(follows); // {"S": {}, "A": {"b"}};
/// ```
pub fn calc_follows(grm: &Grammar, firsts: &HashMap<String, HashSet<String>>)
                    -> HashMap<String, HashSet<String>> {

    // initialise follow set
    let mut follows: HashMap<String, HashSet<String>> = HashMap::new();
    for rule in grm.rules.values() {
        follows.insert(rule.name.clone(), HashSet::new());
    }

    let mut changed;
    loop {
        changed = false;
        for rule in grm.rules.values() {
            for alt in rule.alternatives.iter() {
                for (sym_i, sym) in alt.iter().enumerate() {
                    if sym.typ == SymbolType::Terminal {
                        continue
                    }
                    let mut new = HashSet::new();
                    // add FIRSTS(succeeding symbols) to temporary follow set
                    let followers = alt[sym_i+1..].to_vec();
                    let f = get_firsts_from_symbols(firsts, &followers);
                    for e in f.iter() {
                        if e != "" {
                            new.insert(e.clone());
                        }
                    }
                    // if no symbols are following sym, or FIRST(followers) contains epsilon, then add
                    // FOLLOW(rule.name) to the set as well
                    if followers.len() == 0 || f.contains("") {
                        let rule_follow = follows.get(&rule.name).unwrap();
                        for e in rule_follow {
                            new.insert(e.clone());
                        }
                    }
                    // add everything from temporary set to current follow set
                    let mut old = follows.get_mut(&sym.name).unwrap();
                    for e in new {
                        if !old.contains(&e) {
                            old.insert(e.clone());
                            changed = true;
                        }
                    }
                }
            }
        }
        if !changed {
            return follows;
        }
    }
}
