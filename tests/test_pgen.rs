#[macro_use]

extern crate lrpar;
use lrpar::parse_yacc;
use lrpar::grammar::{Grammar, Symbol, SymbolType};
use lrpar::pgen::calc_firsts;
use std::collections::{HashMap, HashSet};

fn has(firsts: &HashMap<String, HashSet<String>>, n: &str, should_be: Vec<&str>) {
    let f = firsts.get(&n.to_string()).unwrap();
    println!("{:?} {:?}", f, should_be);
    assert!(f.len() == should_be.len());
    for k in should_be.iter() {
        assert!(f.contains(&k.to_string()));
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
    has(&firsts, "D", vec!["d"]);
    has(&firsts, "E", vec!["d", "c"]);
    has(&firsts, "F", vec!["d", "c"]);
}

/*
#[test]
fn test_epsilon() {
    let mut grm = Grammar::new();
    grm.add_rule("A".to_string(), vec!(nonterminal!("B"), terminal!("a")));
    grm.add_rule("B".to_string(), vec!(terminal!("b")));
    grm.add_rule("B".to_string(), vec!(Symbol::new("".to_string(), SymbolType::Epsilon)));

    grm.add_rule("D".to_string(), vec!(nonterminal!("C"), Symbol::new("".to_string(), SymbolType::Epsilon)));
    grm.add_rule("C".to_string(), vec!(terminal!("b")));
    grm.add_rule("C".to_string(), vec!(Symbol::new("".to_string(), SymbolType::Epsilon)));

    let first = First {grm: grm};
    assert_eq!(first.first(&nonterminal!("A")), hset(vec![terminal!("b"), terminal!("a")]));
    assert_eq!(first.first(&nonterminal!("D")), hset(vec![terminal!("b"), Symbol::new("".to_string(), SymbolType::Epsilon)]));
}

#[test]
fn test_double_symbols() {
    let mut grm = Grammar::new();
    grm.add_rule("A".to_string(), vec!(nonterminal!("B"), terminal!("b")));
    grm.add_rule("B".to_string(), vec!(terminal!("b")));
    grm.add_rule("B".to_string(), vec!(Symbol::new("".to_string(), SymbolType::Epsilon)));
    let first = First {grm: grm};
    assert_eq!(first.first(&nonterminal!("A")), hset(vec![terminal!("b")]));
}
*/
