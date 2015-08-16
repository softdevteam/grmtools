use grammar_ast::{GrammarAST, Symbol, nonterminal};
use std::collections::{HashMap, HashSet};
use std::hash::{Hash, Hasher};

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
pub fn calc_firsts(grm: &GrammarAST) -> HashMap<String, HashSet<String>> {
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
            if let &Symbol::Terminal(ref name) = sym {
                f.insert(name.clone());
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
                    match sym {
                        &Symbol::Terminal(ref name) => {
                            // if symbol is a Terminal, add to FIRSTS
                            let mut f = firsts.get_mut(&rul.name).unwrap();
                            if !f.contains(name) {
                                f.insert(name.clone());
                                changed = true;
                            }
                            break;
                        },
                        &Symbol::Nonterminal(ref name) => {
                            // if symbols is Nonterminal, get its FIRSTS and add them to the
                            // current FIRSTS. if the Nonterminals FIRSTS contain an epsilon,
                            // continue looking at the succeeding Nonterminal, otherwise break
                            let of = firsts.get(name).unwrap().clone();
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
        match s {
            &Symbol::Terminal(ref name) => {
                r.insert(name.clone());
                break;
            },
            &Symbol::Nonterminal(ref name) => {
                let f = firsts.get(name).unwrap();
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
pub fn calc_follows(grm: &GrammarAST, firsts: &HashMap<String, HashSet<String>>)
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
                    match sym {
                        &Symbol::Terminal(_) => continue,
                        &Symbol::Nonterminal(ref name) => {
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
                            let mut old = follows.get_mut(name).unwrap();
                            for e in new {
                                if !old.contains(&e) {
                                    old.insert(e.clone());
                                    changed = true;
                                }
                            }
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

#[derive(PartialEq, Eq, Debug)]
/// Implementation of `LR1Item` which is used to build the state graph of a grammar. Consists of a
/// left-hand-side `String`, a right-hand-side list of `Symbols` and an integer `dot`, denoting the
/// current position of the parser inside of `rhs`.
pub struct LR1Item {
    pub lhs: String,
    pub rhs: Vec<Symbol>,
    pub dot: usize,
}

impl LR1Item {
    /// Returns a new LR1Item
    ///
    /// # Example
    ///
    /// ```c
    /// let item = LR1Item::new("S".to_string(), vec![nonterminal!("A".to_string())], 1);
    /// ```
    pub fn new(lhs: String, rhs: Vec<Symbol>, dot: usize) -> LR1Item {
        LR1Item {lhs: lhs, rhs: rhs, dot: dot}
    }

    /// Returns a copy of the `Symbol` at the current position inside the `rhs`.
    ///
    /// # Example
    ///
    /// ```c
    /// let item = LR1Item::new("S".to_string(), vec![nonterminal!("A".to_string()),
    ///                                               terminal!("a".to_string())], 1);
    /// let n = item.next(); // returns terminal!("a")
    /// ```
    pub fn next(&self) -> Option<Symbol>{
        if self.dot < self.rhs.len() {
            let ref sym = self.rhs[self.dot];
            Some(sym.clone())
        }
        else {
            None
        }
    }
}

impl Hash for LR1Item {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.lhs.hash(state);
        self.rhs.hash(state);
        self.dot.hash(state);
    }
}

pub fn lritem(lhs: &str, rhs: Vec<Symbol>, d: usize) -> LR1Item {
    let mut item = LR1Item::new(lhs.to_string(), Vec::new(), d);
    for e in rhs.iter() {
        item.rhs.push(e.clone());
    }
    item
}

pub fn mk_string_hashset(vec: Vec<&str>) -> HashSet<String> {
    let mut hs = HashSet::new();
    for e in vec.iter() {
        hs.insert(e.to_string());
    }
    hs
}

/// Calculates the closure of a HashMap containing LR1Items
pub fn closure1(grm: &GrammarAST, firsts: &HashMap<String, HashSet<String>>,
                closure: &mut HashMap<LR1Item, HashSet<String>>) {
    loop {
        let mut changed = false;
        let mut tmp_closure = Vec::new();
        for (item, la) in closure.iter() {
            // get next symbol after dot
            let next_sym = item.next();
            if next_sym != None {
                match next_sym.unwrap() {
                    // get rule with next_sym at the beginning
                    Symbol::Terminal(_) => continue,
                    Symbol::Nonterminal(name) => {
                        let rule = grm.get_rule(&name).unwrap();
                        // add each alternative as an LR1Item to the closure
                        for alt in rule.alternatives.iter() {
                            let lhs = name.clone();
                            let rhs = alt.clone();
                            let dot = 0;
                            // calculate lookahead
                            let mut newla = HashSet::new();
                            let remaining_symbols = &item.rhs[item.dot+1..];
                            for e in la.iter() {
                                // chain each lookahead with the remaining symbols...
                                let mut chain = Vec::new();
                                // XXX replace with extend/push_all when stable
                                for r in remaining_symbols.iter() {
                                    chain.push(r.clone());
                                }
                                chain.push(Symbol::Terminal(e.clone()));
                                // ..and calculate their first sets...
                                let first = get_firsts_from_symbols(firsts, &chain);
                                // ...and union them together.
                                for f in first.iter() {
                                    newla.insert(f.clone());
                                }
                            }
                            let new_item = LR1Item::new(lhs, rhs, dot);
                            tmp_closure.push((new_item, newla));
                        }
                    }
                }
            }
        }
        // merge new LR1Item candidates into closure map
        for (i, l) in tmp_closure.drain(..) {
            if closure.contains_key(&i) {
                let x = closure.get_mut(&i).unwrap();
                for k in l {
                    if !x.contains(&k) {
                        x.insert(k.clone());
                        changed = true;
                    }
                }
            }
            else {
                closure.insert(i,l);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
}

/// Calculates the goto that results from reading past a certain symbol in another set.
pub fn goto1(grm: &GrammarAST, firsts: &HashMap<String, HashSet<String>>,
             state: &HashMap<LR1Item, HashSet<String>>, symbol: &Symbol)
             -> HashMap<LR1Item, HashSet<String>> {
    let mut goto = HashMap::new();

    for (item, la) in state.iter() {
        if item.next() != None {
            if &item.next().unwrap() == symbol {
                // Clone item and insert into new goto set
                let lhs = item.lhs.clone();
                let rhs = item.rhs.clone();
                let dot = item.dot + 1;
                let gotoitm = LR1Item::new(lhs, rhs, dot);
                let gotola = la.clone();
                goto.insert(gotoitm, gotola);
            }
        }
    }
    closure1(grm, firsts, &mut goto);
    goto
}

pub struct StateGraph {
    pub states: Vec<HashMap<LR1Item, HashSet<String>>>,
    pub edges: HashMap<(i32, Symbol), i32>
}

impl StateGraph {
    pub fn contains(&self, state: &HashMap<LR1Item, HashSet<String>>) -> bool {
        self.states.contains(state)
    }
}

/// Builds a `StateGraph` from the given `Grammar`.
pub fn build_graph(grm: &GrammarAST) -> StateGraph {
    let mut states = Vec::new();
    let mut edges = HashMap::new();
    let mut todo = Vec::new();

    // calculate first sets
    let firsts = calc_firsts(&grm);
    
    // Create first state
    let item = lritem("Start!", vec![nonterminal(&grm.start.clone().unwrap())], 0);
    let mut la = HashSet::new();
    la.insert("$".to_string());
    let mut s0 = HashMap::new();
    s0.insert(item, la);
    closure1(&grm, &firsts, &mut s0);

    // add to list of states as #0
    todo.push(s0);

    let mut current_id = 0;
    let mut unique_id = 1;

    loop {
        if todo.len() == 0 {
            break;
        }
        let state = todo.remove(0);

        let mut symbols_done = HashSet::new();
        for (item, _) in state.iter() {
            let symbol = match item.next() {
                Some(x) => x,
                None => continue
            };
            if symbols_done.contains(&symbol) {
                continue;
            }
            else {
                // Cache processed symbols so that we don't create the same
                // goto set multiple times for different rules with the same
                // next symbol
                symbols_done.insert(symbol.clone());
            }
            let goto = goto1(&grm, &firsts, &state, &symbol);
            // This is slow! We are better off hashing the state HashMaps and making `states` a set
            // instead of a vector.
            // Although on second thought, when we add the weakly_compatible optimisation later we
            // might have to iterate over all states anyway
            match states.iter().position(|s| s == &goto) {
                // If goto is already contained map current_id to its position...
                Some(pos) => {edges.insert((current_id, symbol.clone()), pos as i32); ()},
                // ...otherwise add goto to todo-list and map current_id to its unique_id
                None => {
                    todo.push(goto);
                    edges.insert((current_id, symbol.clone()), unique_id);
                    unique_id += 1;
                    ()
                }
            }
        }

        states.push(state);
        current_id += 1;
    }

    StateGraph {states: states, edges: edges}
}
