extern crate lrpar;
use lrpar::grammar_ast::{Grammar, Symbol, nonterminal, terminal};
use lrpar::pgen::{calc_firsts, calc_follows, LR1Item, closure1, goto1, build_graph,
                  mk_string_hashset, lritem, StateGraph};
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
    grm.add_rule("C".to_string(), vec!(terminal("c")));
    grm.add_rule("D".to_string(), vec!(terminal("d")));
    grm.add_rule("E".to_string(), vec!(nonterminal("D")));
    grm.add_rule("E".to_string(), vec!(nonterminal("C")));
    grm.add_rule("F".to_string(), vec!(nonterminal("E")));
    let firsts = calc_firsts(&grm);
    has(&firsts, "D", vec!["d"]);
    has(&firsts, "E", vec!["d", "c"]);
    has(&firsts, "F", vec!["d", "c"]);
}

#[test]
fn test_first_no_subsequent_nonterminals() {
    let mut grm = Grammar::new();
    grm.add_rule("C".to_string(), vec!(terminal("c")));
    grm.add_rule("D".to_string(), vec!(terminal("d")));
    grm.add_rule("E".to_string(), vec!(nonterminal("D"), nonterminal("C")));
    let firsts = calc_firsts(&grm);
    has(&firsts, "E", vec!["d"]);
}

#[test]
fn test_first_epsilon() {
    let mut grm = Grammar::new();
    grm.add_rule("A".to_string(), vec!(nonterminal("B"), terminal("a")));
    grm.add_rule("B".to_string(), vec!(terminal("b")));
    grm.add_rule("B".to_string(), vec!());

    grm.add_rule("D".to_string(), vec!(nonterminal("C")));
    grm.add_rule("C".to_string(), vec!(terminal("c")));
    grm.add_rule("C".to_string(), vec!());

    let firsts = calc_firsts(&grm);
    has(&firsts, "A", vec!["b", "a"]);
    has(&firsts, "C", vec!["c", ""]);
    has(&firsts, "D", vec!["c", ""]);
}

#[test]
fn test_last_epsilon() {
    let mut grm = Grammar::new();
    grm.add_rule("A".to_string(), vec!(nonterminal("B"), nonterminal("C")));
    grm.add_rule("B".to_string(), vec!(terminal("b")));
    grm.add_rule("B".to_string(), vec!());
    grm.add_rule("C".to_string(), vec!(nonterminal("B"), terminal("c"), nonterminal("B")));

    let firsts = calc_firsts(&grm);
    has(&firsts, "A", vec!["b", "c"]);
    has(&firsts, "B", vec!["b", ""]);
    has(&firsts, "C", vec!["b", "c"]);
}

#[test]
fn test_first_no_multiples() {
    let mut grm = Grammar::new();
    grm.add_rule("A".to_string(), vec!(nonterminal("B"), terminal("b")));
    grm.add_rule("B".to_string(), vec!(terminal("b")));
    grm.add_rule("B".to_string(), vec!());
    let firsts = calc_firsts(&grm);
    has(&firsts, "A", vec!["b"]);
}

fn eco_grammar() -> Grammar {
    let mut grm = Grammar::new();
    grm.add_rule("Z".to_string(), vec!(nonterminal("S")));
    grm.add_rule("S".to_string(), vec!(nonterminal("S"), terminal("b")));
    grm.add_rule("S".to_string(), vec!(terminal("b"), nonterminal("A"), terminal("a")));
    grm.add_rule("S".to_string(), vec!(terminal("a")));
    grm.add_rule("A".to_string(), vec!(terminal("a"), nonterminal("S"), terminal("c")));
    grm.add_rule("A".to_string(), vec!(terminal("a")));
    grm.add_rule("A".to_string(), vec!(terminal("a"), nonterminal("S"), terminal("b")));
    grm.add_rule("B".to_string(), vec!(nonterminal("A"), nonterminal("S")));
    grm.add_rule("C".to_string(), vec!(nonterminal("D"), nonterminal("A")));
    grm.add_rule("D".to_string(), vec!(terminal("d")));
    grm.add_rule("D".to_string(), vec!());
    grm.add_rule("F".to_string(), vec!(nonterminal("C"), nonterminal("D"), terminal("f")));
    grm
}

#[test]
fn test_first_from_eco() {
    let grm = eco_grammar();
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
    let grm = eco_grammar();
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
    grm.add_rule("E".to_string(), vec!(nonterminal("T")));
    grm.add_rule("E".to_string(), vec!(nonterminal("E"), terminal("+"), nonterminal("T")));
    grm.add_rule("T".to_string(), vec!(nonterminal("P")));
    grm.add_rule("T".to_string(), vec!(nonterminal("T"), terminal("*"), nonterminal("P")));
    grm.add_rule("P".to_string(), vec!(terminal("a")));
    grm.add_rule("C".to_string(), vec!(nonterminal("C"), terminal("c")));
    grm.add_rule("C".to_string(), vec!());
    grm.add_rule("D".to_string(), vec!(nonterminal("D"), terminal("d")));
    grm.add_rule("D".to_string(), vec!(nonterminal("F")));
    grm.add_rule("F".to_string(), vec!(terminal("f")));
    grm.add_rule("F".to_string(), vec!());
    grm.add_rule("G".to_string(), vec!(nonterminal("C"), nonterminal("D")));

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
    grm.add_rule("E".to_string(), vec!(nonterminal("T"), nonterminal("P")));
    grm.add_rule("P".to_string(), vec!(terminal("+"), nonterminal("T"), nonterminal("P")));
    grm.add_rule("P".to_string(), vec!());
    grm.add_rule("T".to_string(), vec!(nonterminal("F"), nonterminal("Q")));
    grm.add_rule("Q".to_string(), vec!(terminal("*"), nonterminal("F"), nonterminal("Q")));
    grm.add_rule("Q".to_string(), vec!());
    grm.add_rule("F".to_string(), vec!(terminal("("), nonterminal("E"), terminal(")")));
    grm.add_rule("F".to_string(), vec!(terminal("id")));
    grm
}

#[test]
fn test_grammar2() {
    let grm = grammar2();
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

#[test]
fn test_lrelements() {
    let mut e = LR1Item::new("S".to_string(), vec![nonterminal("A"), terminal("b")], 0);
    assert_eq!(e.lhs, "S");
    assert_eq!(e.rhs, vec![nonterminal("A"), terminal("b")]);
    assert_eq!(e.dot, 0);
    assert_eq!(e.next().unwrap(), nonterminal("A"));

    e.dot = 1;
    assert_eq!(e.next().unwrap(), terminal("b"));
}

#[test]
fn test_closure1_ecogrm() {
    let grm = eco_grammar();
    let firsts = calc_firsts(&grm);

    let item = lritem("Z", vec![nonterminal("S")], 0);
    let la = mk_string_hashset(vec!["$"]);
    let mut state = HashMap::new();
    state.insert(item, la);
    closure1(&grm, &firsts, &mut state);

    let c0 = lritem("Z", vec![nonterminal("S")], 0);
    let c1 = lritem("S", vec![nonterminal("S"), terminal("b")], 0);
    let c2 = lritem("S", vec![terminal("b"), nonterminal("A"), terminal("a")], 0);
    let c3 = lritem("S", vec![terminal("a")], 0);
    assert_eq!(state.get(&c0).unwrap(), &mk_string_hashset(vec!["$"]));
    assert_eq!(state.get(&c1).unwrap(), &mk_string_hashset(vec!["b", "$"]));
    assert_eq!(state.get(&c2).unwrap(), &mk_string_hashset(vec!["b", "$"]));
    assert_eq!(state.get(&c3).unwrap(), &mk_string_hashset(vec!["b", "$"]));

    let item2 = lritem("F", vec![nonterminal("C"), nonterminal("D"), terminal("f")], 0);
    let la2 = mk_string_hashset(vec!["$"]);
    let mut state2 = HashMap::new();
    state2.insert(item2, la2);
    closure1(&grm, &firsts, &mut state2);

    let c4 = lritem("F", vec![nonterminal("C"), nonterminal("D"), terminal("f")], 0);
    let c5 = lritem("C", vec![nonterminal("D"), nonterminal("A")], 0);
    let c6 = lritem("D", vec![terminal("d")], 0);
    let c7 = lritem("D", vec![], 0);
    assert_eq!(state2.get(&c4).unwrap(), &mk_string_hashset(vec!["$"]));
    assert_eq!(state2.get(&c5).unwrap(), &mk_string_hashset(vec!["d", "f"]));
    assert_eq!(state2.get(&c6).unwrap(), &mk_string_hashset(vec!["a"]));
    assert_eq!(state2.get(&c7).unwrap(), &mk_string_hashset(vec!["a"]));
}

// Grammar from 'LR(k) Analyse fuer Pragmatiker'
// Z : S
// S : Sb
//     bAa
// A : aSc
//     a
//     aSb
fn grammar3() -> Grammar {
    let mut grm = Grammar::new();
    grm.add_rule("Z".to_string(), vec!(nonterminal("S")));
    grm.add_rule("S".to_string(), vec!(nonterminal("S"), terminal("b")));
    grm.add_rule("S".to_string(), vec!(terminal("b"), nonterminal("A"), terminal("a")));
    grm.add_rule("A".to_string(), vec!(terminal("a"), nonterminal("S"), terminal("c")));
    grm.add_rule("A".to_string(), vec!(terminal("a")));
    grm.add_rule("A".to_string(), vec!(terminal("a"), nonterminal("S"), terminal("b")));
    grm.start = "Z".to_string();
    grm
}

#[test]
fn test_closure1_grm3() {
    let grm = grammar3();
    let firsts = calc_firsts(&grm);

    let item = lritem("Z", vec![nonterminal("S")], 0);
    let la = mk_string_hashset(vec!["$"]);
    let mut state = HashMap::new();
    state.insert(item, la);
    closure1(&grm, &firsts, &mut state);

    let c0 = lritem("Z", vec![nonterminal("S")], 0);
    let c1 = lritem("S", vec![nonterminal("S"), terminal("b")], 0);
    let c2 = lritem("S", vec![terminal("b"), nonterminal("A"), terminal("a")], 0);
    assert_eq!(state.get(&c0).unwrap(), &mk_string_hashset(vec!["$"]));
    assert_eq!(state.get(&c1).unwrap(), &mk_string_hashset(vec!["b", "$"]));
    assert_eq!(state.get(&c2).unwrap(), &mk_string_hashset(vec!["b", "$"]));

    let item2 = lritem("S", vec![terminal("b"), nonterminal("A"), terminal("a")], 1);
    let la2 = mk_string_hashset(vec!["$", "b"]);
    let mut state2 = HashMap::new();
    state2.insert(item2, la2);
    closure1(&grm, &firsts, &mut state2);

    let c3 = lritem("A", vec![terminal("a"), nonterminal("S"), terminal("c")], 0);
    let c4 = lritem("A", vec![terminal("a")], 0);
    let c5 = lritem("A", vec![terminal("a"), nonterminal("S"), terminal("b")], 0);

    assert_eq!(state2.get(&c3).unwrap(), &mk_string_hashset(vec!["a"]));
    assert_eq!(state2.get(&c4).unwrap(), &mk_string_hashset(vec!["a"]));
    assert_eq!(state2.get(&c5).unwrap(), &mk_string_hashset(vec!["a"]));

    let item3 = lritem("A", vec![terminal("a"), nonterminal("S"), terminal("c")], 1);
    let la3 = mk_string_hashset(vec!["a"]);
    let mut state3 = HashMap::new();
    state3.insert(item3, la3);
    closure1(&grm, &firsts, &mut state3);

    let c8 = lritem("S", vec![nonterminal("S"), terminal("b")], 0);
    let c9 = lritem("S", vec![terminal("b"), nonterminal("A"), terminal("a")], 0);

    assert_eq!(state3.get(&c8).unwrap(), &mk_string_hashset(vec!["b", "c"]));
    assert_eq!(state3.get(&c9).unwrap(), &mk_string_hashset(vec!["b", "c"]));
}

#[test]
fn test_goto1() {
    let grm = grammar3();
    let firsts = calc_firsts(&grm);

    let item = lritem("Z", vec![nonterminal("S")], 0);
    let la = mk_string_hashset(vec!["$"]);
    let mut state = HashMap::new();
    state.insert(item, la);
    closure1(&grm, &firsts, &mut state);

    // follow 'S' from start set
    let goto = goto1(&grm, &firsts, &state, &nonterminal("S"));

    let g1 = lritem("Z", vec![nonterminal("S")], 1);
    let g2 = lritem("S", vec![nonterminal("S"), terminal("b")], 1);

    assert_eq!(goto.get(&g1).unwrap(), &mk_string_hashset(vec!["$"]));
    assert_eq!(goto.get(&g2).unwrap(), &mk_string_hashset(vec!["$", "b"]));

    // follow 'b' from start set
    let goto2 = goto1(&grm, &firsts, &state, &terminal("b"));

    let g3 = lritem("S", vec![terminal("b"), nonterminal("A"), terminal("a")], 1);
    let g4 = lritem("A", vec![terminal("a"), nonterminal("S"), terminal("c")], 0);
    let g5 = lritem("A", vec![terminal("a")], 0);
    let g6 = lritem("A", vec![terminal("a"), nonterminal("S"), terminal("b")], 0);

    assert_eq!(goto2.get(&g3).unwrap(), &mk_string_hashset(vec!["$", "b"]));
    assert_eq!(goto2.get(&g4).unwrap(), &mk_string_hashset(vec!["a"]));
    assert_eq!(goto2.get(&g5).unwrap(), &mk_string_hashset(vec!["a"]));
    assert_eq!(goto2.get(&g6).unwrap(), &mk_string_hashset(vec!["a"]));

    // continue by following 'a' from last goto
    let goto3 = goto1(&grm, &firsts, &goto2, &terminal("a"));

    let g31 = lritem("A", vec![terminal("a"), nonterminal("S"), terminal("c")], 1);
    let g32 = lritem("A", vec![terminal("a")], 1);
    let g33 = lritem("A", vec![terminal("a"), nonterminal("S"), terminal("b")], 1);
    let g34 = lritem("S", vec![nonterminal("S"), terminal("b")], 0);
    let g35 = lritem("S", vec![terminal("b"), nonterminal("A"), terminal("a")], 0);

    assert_eq!(goto3.get(&g31).unwrap(), &mk_string_hashset(vec!["a"]));
    assert_eq!(goto3.get(&g32).unwrap(), &mk_string_hashset(vec!["a"]));
    assert_eq!(goto3.get(&g33).unwrap(), &mk_string_hashset(vec!["a"]));
    assert_eq!(goto3.get(&g34).unwrap(), &mk_string_hashset(vec!["c", "b"]));
    assert_eq!(goto3.get(&g35).unwrap(), &mk_string_hashset(vec!["c", "b"]));

}

#[test]
fn test_stategraph() {
    let grm = grammar3();
    let graph = build_graph(&grm);

    // State 0
    let mut s0 = HashMap::new();
    s0.insert(lritem("Start!", vec![nonterminal("Z")], 0), mk_string_hashset(vec!["$"]));
    s0.insert(lritem("Z", vec![nonterminal("S")], 0), mk_string_hashset(vec!["$"]));
    s0.insert(lritem("S", vec![nonterminal("S"), terminal("b")], 0), mk_string_hashset(vec!["$", "b"]));
    s0.insert(lritem("S", vec![terminal("b"), nonterminal("A"), terminal("a")], 0), mk_string_hashset(vec!["$", "b"]));

    // State 1
    let mut s1 = HashMap::new();
    s1.insert(lritem("Start!", vec![nonterminal("Z")], 1), mk_string_hashset(vec!["$"]));

    // State 2
    let mut s2 = HashMap::new();
    s2.insert(lritem("Z", vec![nonterminal("S")], 1), mk_string_hashset(vec!["$"]));
    s2.insert(lritem("S", vec![nonterminal("S"), terminal("b")], 1), mk_string_hashset(vec!["$", "b"]));

    // State 3
    let mut s3 = HashMap::new();
    s3.insert(lritem("S", vec![terminal("b"), nonterminal("A"), terminal("a")], 1), mk_string_hashset(vec!["$", "b"]));
    s3.insert(lritem("A", vec![terminal("a"), nonterminal("S"), terminal("c")], 0), mk_string_hashset(vec!["a"]));
    s3.insert(lritem("A", vec![terminal("a")], 0), mk_string_hashset(vec!["a"]));
    s3.insert(lritem("A", vec![terminal("a"), nonterminal("S"), terminal("b")], 0), mk_string_hashset(vec!["a"]));

    // State 4
    let mut s4 = HashMap::new();
    s4.insert(lritem("S", vec![nonterminal("S"), terminal("b")], 2), mk_string_hashset(vec!["$", "b"]));

    // State 5
    let mut s5 = HashMap::new();
    s5.insert(lritem("A", vec![terminal("a"), nonterminal("S"), terminal("c")], 1), mk_string_hashset(vec!["a"]));
    s5.insert(lritem("A", vec![terminal("a")], 1), mk_string_hashset(vec!["a"]));
    s5.insert(lritem("A", vec![terminal("a"), nonterminal("S"), terminal("b")], 1), mk_string_hashset(vec!["a"]));
    s5.insert(lritem("S", vec![nonterminal("S"), terminal("b")], 0), mk_string_hashset(vec!["c", "b"]));
    s5.insert(lritem("S", vec![terminal("b"), nonterminal("A"), terminal("a")], 0), mk_string_hashset(vec!["c", "b"]));

    // State 6
    let mut s6 = HashMap::new();
    s6.insert(lritem("S", vec![terminal("b"), nonterminal("A"), terminal("a")], 2), mk_string_hashset(vec!["$", "b"]));

    // State 7
    let mut s7 = HashMap::new();
    s7.insert(lritem("A", vec![terminal("a"), nonterminal("S"), terminal("c")], 2), mk_string_hashset(vec!["a"]));
    s7.insert(lritem("A", vec![terminal("a"), nonterminal("S"), terminal("b")], 2), mk_string_hashset(vec!["a"]));
    s7.insert(lritem("S", vec![nonterminal("S"), terminal("b")], 1), mk_string_hashset(vec!["c", "b"]));

    // State 8
    let mut s8 = HashMap::new();
    s8.insert(lritem("S", vec![terminal("b"), nonterminal("A"), terminal("a")], 1), mk_string_hashset(vec!["c", "b"]));
    s8.insert(lritem("A", vec![terminal("a"), nonterminal("S"), terminal("c")], 0), mk_string_hashset(vec!["a"]));
    s8.insert(lritem("A", vec![terminal("a")], 0), mk_string_hashset(vec!["a"]));
    s8.insert(lritem("A", vec![terminal("a"), nonterminal("S"), terminal("b")], 0), mk_string_hashset(vec!["a"]));

    // State 9
    let mut s9 = HashMap::new();
    s9.insert(lritem("S", vec![terminal("b"), nonterminal("A"), terminal("a")], 3), mk_string_hashset(vec!["$", "b"]));

    // State 10
    let mut s10 = HashMap::new();
    s10.insert(lritem("A", vec![terminal("a"), nonterminal("S"), terminal("b")], 3), mk_string_hashset(vec!["a"]));
    s10.insert(lritem("S", vec![nonterminal("S"), terminal("b")], 2), mk_string_hashset(vec!["c", "b"]));

    // State 11
    let mut s11 = HashMap::new();
    s11.insert(lritem("A", vec![terminal("a"), nonterminal("S"), terminal("c")], 3), mk_string_hashset(vec!["a"]));

    // State 12
    let mut s12 = HashMap::new();
    s12.insert(lritem("S", vec![terminal("b"), nonterminal("A"), terminal("a")], 2), mk_string_hashset(vec!["c", "b"]));

    // State 13
    let mut s13 = HashMap::new();
    s13.insert(lritem("S", vec![terminal("b"), nonterminal("A"), terminal("a")], 3), mk_string_hashset(vec!["c", "b"]));

    // test states
    assert!(graph.states.len() == 14);
    assert!(graph.contains(&s0));
    assert!(graph.contains(&s1));
    assert!(graph.contains(&s2));
    assert!(graph.contains(&s3));
    assert!(graph.contains(&s4));
    assert!(graph.contains(&s5));
    assert!(graph.contains(&s6));
    assert!(graph.contains(&s7));
    assert!(graph.contains(&s8));
    assert!(graph.contains(&s9));
    assert!(graph.contains(&s10));
    assert!(graph.contains(&s11));
    assert!(graph.contains(&s12));
    assert!(graph.contains(&s13));

    // test edges
    test_edge(&graph, &s0, nonterminal("Z"), &s1);
    test_edge(&graph, &s0, nonterminal("S"), &s2);
    test_edge(&graph, &s0, terminal("b"), &s3);
    test_edge(&graph, &s2, terminal("b"), &s4);
    test_edge(&graph, &s3, nonterminal("A"), &s6);
    test_edge(&graph, &s3, terminal("a"), &s5);
    test_edge(&graph, &s5, nonterminal("S"), &s7);
    test_edge(&graph, &s5, terminal("b"), &s8);
    test_edge(&graph, &s6, terminal("a"), &s9);
    test_edge(&graph, &s7, terminal("c"), &s11);
    test_edge(&graph, &s7, terminal("b"), &s10);
    test_edge(&graph, &s8, terminal("a"), &s5);
    test_edge(&graph, &s8, nonterminal("A"), &s12);
    test_edge(&graph, &s12, terminal("a"), &s13);
}

fn test_edge(graph: &StateGraph, state: &HashMap<LR1Item, HashSet<String>>, symbol: Symbol, other: &HashMap<LR1Item, HashSet<String>>) {
    let pos = graph.states.iter().position(|s| s == state).unwrap();
    let pos_other = graph.edges.get(&(pos as i32, symbol)).unwrap().clone() as usize;
    assert!(graph.states.get(pos_other).unwrap() == other);
}
