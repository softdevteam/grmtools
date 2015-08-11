#[macro_use]

extern crate lrpar;
use lrpar::parse_yacc;
use lrpar::grammar::{Grammar, Symbol, SymbolType};
use lrpar::pgen::{calc_firsts, calc_follows, get_firsts_from_symbols};
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
    let firsts = calc_firsts(&grm);
    has(&firsts, "D", vec!["d"]);
    has(&firsts, "E", vec!["d", "c"]);
    has(&firsts, "F", vec!["d", "c"]);
}

#[test]
fn test_first_no_subsequent_nonterminals() {
    let mut grm = Grammar::new();
    grm.add_rule("C".to_string(), vec!(terminal!("c")));
    grm.add_rule("D".to_string(), vec!(terminal!("d")));
    grm.add_rule("E".to_string(), vec!(nonterminal!("D"), nonterminal!("C")));
    let firsts = calc_firsts(&grm);
    has(&firsts, "E", vec!["d"]);
}

#[test]
fn test_first_epsilon() {
    let mut grm = Grammar::new();
    grm.add_rule("A".to_string(), vec!(nonterminal!("B"), terminal!("a")));
    grm.add_rule("B".to_string(), vec!(terminal!("b")));
    grm.add_rule("B".to_string(), vec!());

    grm.add_rule("D".to_string(), vec!(nonterminal!("C")));
    grm.add_rule("C".to_string(), vec!(terminal!("c")));
    grm.add_rule("C".to_string(), vec!());

    let firsts = calc_firsts(&grm);
    has(&firsts, "A", vec!["b", "a"]);
    has(&firsts, "C", vec!["c", ""]);
    has(&firsts, "D", vec!["c", ""]);
}

#[test]
fn test_last_epsilon() {
    let mut grm = Grammar::new();
    grm.add_rule("A".to_string(), vec!(nonterminal!("B"), nonterminal!("C")));
    grm.add_rule("B".to_string(), vec!(terminal!("b")));
    grm.add_rule("B".to_string(), vec!());
    grm.add_rule("C".to_string(), vec!(nonterminal!("B"), terminal!("c"), nonterminal!("B")));

    let firsts = calc_firsts(&grm);
    has(&firsts, "A", vec!["b", "c"]);
    has(&firsts, "B", vec!["b", ""]);
    has(&firsts, "C", vec!["b", "c"]);
}

#[test]
fn test_first_no_multiples() {
    let mut grm = Grammar::new();
    grm.add_rule("A".to_string(), vec!(nonterminal!("B"), terminal!("b")));
    grm.add_rule("B".to_string(), vec!(terminal!("b")));
    grm.add_rule("B".to_string(), vec!());
    let firsts = calc_firsts(&grm);
    has(&firsts, "A", vec!["b"]);
}

fn eco_grammar() -> Grammar {
    let mut grm = Grammar::new();
    grm.add_rule("Z".to_string(), vec!(nonterminal!("S")));
    grm.add_rule("S".to_string(), vec!(nonterminal!("S"), terminal!("b")));
    grm.add_rule("S".to_string(), vec!(terminal!("b"), nonterminal!("A"), terminal!("a")));
    grm.add_rule("S".to_string(), vec!(terminal!("a")));
    grm.add_rule("A".to_string(), vec!(terminal!("a"), nonterminal!("S"), terminal!("c")));
    grm.add_rule("A".to_string(), vec!(terminal!("a")));
    grm.add_rule("A".to_string(), vec!(terminal!("a"), nonterminal!("S"), terminal!("b")));
    grm.add_rule("B".to_string(), vec!(nonterminal!("A"), nonterminal!("S")));
    grm.add_rule("C".to_string(), vec!(nonterminal!("D"), nonterminal!("A")));
    grm.add_rule("D".to_string(), vec!(terminal!("d")));
    grm.add_rule("D".to_string(), vec!());
    grm.add_rule("F".to_string(), vec!(nonterminal!("C"), nonterminal!("D"), terminal!("f")));
    grm
}

#[test]
fn test_first_from_eco() {
    let mut grm = eco_grammar();
    let firsts = calc_firsts(&grm);
    has(&firsts, "S", vec!["a", "b"]);
    has(&firsts, "A", vec!["a"]);
    has(&firsts, "B", vec!["a"]);
    has(&firsts, "D", vec!["d", ""]);
    has(&firsts, "C", vec!["d", "a"]);
    has(&firsts, "F", vec!["d", "a"]);
}

#[test]
fn test_follow_from_eco() {
    let mut grm = eco_grammar();
    let firsts = calc_firsts(&grm);
    let follow = calc_follows(&grm, &firsts);
    has(&follow, "S", vec!["b", "c"]);
    has(&follow, "A", vec!["a", "b", "d", "f"]);
    has(&follow, "B", vec![]);
    has(&follow, "C", vec!["d", "f"]);
    has(&follow, "D", vec!["a", "f"]);
}

#[test]
fn test_first_from_eco_bug() {
    let mut grm = Grammar::new();
    grm.add_rule("E".to_string(), vec!(nonterminal!("T")));
    grm.add_rule("E".to_string(), vec!(nonterminal!("E"), terminal!("+"), nonterminal!("T")));
    grm.add_rule("T".to_string(), vec!(nonterminal!("P")));
    grm.add_rule("T".to_string(), vec!(nonterminal!("T"), terminal!("*"), nonterminal!("P")));
    grm.add_rule("P".to_string(), vec!(terminal!("a")));
    grm.add_rule("C".to_string(), vec!(nonterminal!("C"), terminal!("c")));
    grm.add_rule("C".to_string(), vec!());
    grm.add_rule("D".to_string(), vec!(nonterminal!("D"), terminal!("d")));
    grm.add_rule("D".to_string(), vec!(nonterminal!("F")));
    grm.add_rule("F".to_string(), vec!(terminal!("f")));
    grm.add_rule("F".to_string(), vec!());
    grm.add_rule("G".to_string(), vec!(nonterminal!("C"), nonterminal!("D")));

    let firsts = calc_firsts(&grm);
    has(&firsts, "E", vec!["a"]);
    has(&firsts, "T", vec!["a"]);
    has(&firsts, "P", vec!["a"]);
    has(&firsts, "C", vec!["c", ""]);
    has(&firsts, "D", vec!["f", "d", ""]);
    has(&firsts, "G", vec!["c", "d", "f", ""]);
}

fn grammar2() -> Grammar {
    let mut grm = Grammar::new();
    grm.add_rule("E".to_string(), vec!(nonterminal!("T"), nonterminal!("P")));
    grm.add_rule("P".to_string(), vec!(terminal!("+"), nonterminal!("T"), nonterminal!("P")));
    grm.add_rule("P".to_string(), vec!());
    grm.add_rule("T".to_string(), vec!(nonterminal!("F"), nonterminal!("Q")));
    grm.add_rule("Q".to_string(), vec!(terminal!("*"), nonterminal!("F"), nonterminal!("Q")));
    grm.add_rule("Q".to_string(), vec!());
    grm.add_rule("F".to_string(), vec!(terminal!("("), nonterminal!("E"), terminal!(")")));
    grm.add_rule("F".to_string(), vec!(terminal!("id")));
    grm
}

#[test]
fn test_grammar2() {
    let mut grm = grammar2();
    let firsts = calc_firsts(&grm);
    let follow = calc_follows(&grm, &firsts);
    has(&firsts, "E", vec!["(", "id"]);
    has(&firsts, "P", vec!["+", ""]);
    has(&firsts, "T", vec!["(", "id"]);
    has(&firsts, "Q", vec!["*", ""]);
    has(&firsts, "F", vec!["(", "id"]);

    has(&follow, "E", vec![")"]);
    has(&follow, "P", vec![")"]);
    has(&follow, "T", vec!["+",")"]);
    has(&follow, "Q", vec!["+",")"]);
    has(&follow, "F", vec!["*", "+", ")"]);
}
