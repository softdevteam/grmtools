#[macro_use]
extern crate lrpar;
use lrpar::parse_yacc;
use lrpar::grammar::{Grammar, Symbol, SymbolType};
use lrpar::pgen::First;
use std::collections::HashSet;

fn hset(v: Vec<Symbol>) -> HashSet<Symbol> {
    let mut h = HashSet::new();
    for e in v.iter() {
        h.insert(e.clone());
    }
    h
}

#[test]
fn test_first(){
    let mut grm = Grammar::new();
    grm.add_rule("C".to_string(), vec!(terminal!("c")));
    grm.add_rule("D".to_string(), vec!(terminal!("d")));
    grm.add_rule("E".to_string(), vec!(nonterminal!("D")));
    grm.add_rule("E".to_string(), vec!(nonterminal!("C")));
    grm.add_rule("F".to_string(), vec!(nonterminal!("E")));
    let first = First {grm: grm};
    assert_eq!(first.first(&terminal!("a")), hset(vec![terminal!("a")]));
    assert_eq!(first.first(&nonterminal!("D")), hset(vec![terminal!("d")]));
    assert_eq!(first.first(&nonterminal!("E")), hset(vec![terminal!("d"), terminal!("c")]));
    assert_eq!(first.first(&nonterminal!("F")), hset(vec![terminal!("d"), terminal!("c")]));
}

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
