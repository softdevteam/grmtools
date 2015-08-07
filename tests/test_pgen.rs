#[macro_use]

extern crate lrpar;
use lrpar::parse_yacc;
use lrpar::grammar::{Grammar, Symbol, SymbolType};
use lrpar::pgen::calc_firsts;
use std::collections::{HashMap, HashSet};

fn has(firsts: &HashMap<String, HashSet<Symbol>>, n: &str, should_be: Vec<Symbol>) {
    let f = firsts.get(&n.to_string()).unwrap();
    println!("{:?} {:?}", f, should_be);
    assert!(f.len() == should_be.len());
    for k in should_be.iter() {
        assert!(f.contains(&k));
    }
}

#[test]
fn test_first(){
    let mut grm = Grammar::new();
    grm.add_rule("C".to_string(), vec!(terminal!("c")));
    grm.add_rule("D".to_string(), vec!(terminal!("d")));
    grm.add_rule("E".to_string(), vec!(nonterminal!("D")));
    grm.add_rule("E".to_string(), vec!(nonterminal!("C")));
    grm.add_rule("F".to_string(), vec!(nonterminal!("E")));
    let firsts = calc_firsts(grm);
    has(&firsts, "D", vec![terminal!("d")]);
    has(&firsts, "E", vec![terminal!("d"), terminal!("c")]);
    has(&firsts, "F", vec![terminal!("d"), terminal!("c")]);
}

#[test]
fn test_first_no_subsequent_nonterminals() {
    let mut grm = Grammar::new();
    grm.add_rule("C".to_string(), vec!(terminal!("c")));
    grm.add_rule("D".to_string(), vec!(terminal!("d")));
    grm.add_rule("E".to_string(), vec!(nonterminal!("D"), nonterminal!("C")));
    let firsts = calc_firsts(grm);
    has(&firsts, "E", vec![terminal!("d")]);
}

#[test]
fn test_frst_epsilon() {
    let mut grm = Grammar::new();
    grm.add_rule("A".to_string(), vec!(nonterminal!("B"), terminal!("a")));
    grm.add_rule("B".to_string(), vec!(terminal!("b")));
    grm.add_rule("B".to_string(), vec!(Symbol::new("".to_string(), SymbolType::Epsilon)));

    grm.add_rule("D".to_string(), vec!(nonterminal!("C")));
    grm.add_rule("C".to_string(), vec!(terminal!("c")));
    grm.add_rule("C".to_string(), vec!(Symbol::new("".to_string(), SymbolType::Epsilon)));

    let firsts = calc_firsts(grm);
    has(&firsts, "A", vec![terminal!("b"), terminal!("a")]);
    has(&firsts, "C", vec![terminal!("c"), Symbol::new("".to_string(), SymbolType::Epsilon)]);
    has(&firsts, "D", vec![terminal!("c"), Symbol::new("".to_string(), SymbolType::Epsilon)]);
}

#[test]
fn test_first_no_multiples() {
    let mut grm = Grammar::new();
    grm.add_rule("A".to_string(), vec!(nonterminal!("B"), terminal!("b")));
    grm.add_rule("B".to_string(), vec!(terminal!("b")));
    grm.add_rule("B".to_string(), vec!(Symbol::new("".to_string(), SymbolType::Epsilon)));
    let firsts = calc_firsts(grm);
    has(&firsts, "A", vec![terminal!("b")]);
}
