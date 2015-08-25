extern crate bit_vec;
use self::bit_vec::BitVec;

extern crate lrpar;
use lrpar::grammar::{AIdx, ast_to_grammar, Grammar, Symbol};
use lrpar::yacc::parse_yacc;
//use lrpar::pgen::{calc_firsts, calc_follows, LR1Item, closure1, goto1};
use lrpar::pgen::{Itemset, Firsts};

fn has(grm: &Grammar, firsts: &Firsts, rn: &str, should_be: Vec<&str>) {
    let nt_i = grm.nonterminal_off(rn);
    println!("{:?} {} {:?} {:?}", firsts, rn, should_be, grm.terminal_names);
    for (i, n) in grm.terminal_names.iter().enumerate() {
        println!("matching {} {} {:?} {:?}", i, n, should_be.iter().position(|x| x == n), firsts.is_set(nt_i, i));
        match should_be.iter().position(|x| x == n) {
            Some(_) => {
                if !firsts.is_set(nt_i, i) {
                    panic!("{} is not set in {}", n, rn);
                }
            }
            None    => {
                if firsts.is_set(nt_i, i) {
                    panic!("{} is incorrectly set in {}", n, rn);
                }
            }
        }
    }
    if should_be.iter().position(|x| x == &"".to_string()).is_some() {
        assert!(firsts.is_epsilon_set(nt_i));
    }
}

#[test]
fn test_first(){
    let ast = parse_yacc(&"
      %start C
      %token c d
      %%
      C: 'c';
      D: 'd';
      E: D | C;
      F: E;
      ".to_string()).unwrap();
    let grm = ast_to_grammar(&ast);
    let firsts = Firsts::new(&grm);
    has(&grm, &firsts, "^", vec!["c"]);
    has(&grm, &firsts, "D", vec!["d"]);
    has(&grm, &firsts, "E", vec!["d", "c"]);
    has(&grm, &firsts, "F", vec!["d", "c"]);
}

#[test]
fn test_first_no_subsequent_nonterminals() {
    let ast = parse_yacc(&"
      %start C
      %token c d
      %%
      C: 'c';
      D: 'd';
      E: D C;
      ".to_string()).unwrap();
    let grm = ast_to_grammar(&ast);
    let firsts = Firsts::new(&grm);
    has(&grm, &firsts, "E", vec!["d"]);
}

#[test]
fn test_first_epsilon() {
    let ast = parse_yacc(&"
      %start A
      %token a b c
      %%
      A: B 'a';
      B: 'b' | ;
      C: 'c' | ;
      D: C;
      ".to_string()).unwrap();
    let grm = ast_to_grammar(&ast);
    let firsts = Firsts::new(&grm);
    has(&grm, &firsts, "A", vec!["b", "a"]);
    has(&grm, &firsts, "C", vec!["c", ""]);
    has(&grm, &firsts, "D", vec!["c", ""]);
}

#[test]
fn test_last_epsilon() {
    let ast = parse_yacc(&"
      %start A
      %token b c
      %%
      A: B C;
      B: 'b' | ;
      C: B 'c' B;
      ".to_string()).unwrap();
    let grm = ast_to_grammar(&ast);
    let firsts = Firsts::new(&grm);
    has(&grm, &firsts, "A", vec!["b", "c"]);
    has(&grm, &firsts, "B", vec!["b", ""]);
    has(&grm, &firsts, "C", vec!["b", "c"]);
}

#[test]
fn test_first_no_multiples() {
    let ast = parse_yacc(&"
      %start A
      %token b c
      %%
      A: B 'b';
      B: 'b' | ;
      ".to_string()).unwrap();
    let grm = ast_to_grammar(&ast);
    let firsts = Firsts::new(&grm);
    has(&grm, &firsts, "A", vec!["b"]);
}

fn eco_grammar() -> Grammar {
    let ast = parse_yacc(&"
      %start S
      %token a b c d f
      %%
      S: S 'b' | 'b' A 'a' | 'a';
      A: 'a' S 'c' | 'a' | 'a' S 'b';
      B: A S;
      C: D A;
      D: 'd' | ;
      F: C D 'f';
      ".to_string()).unwrap();
    ast_to_grammar(&ast)
}

#[test]
fn test_first_from_eco() {
    let grm = eco_grammar();
    let firsts = Firsts::new(&grm);
    has(&grm, &firsts, "S", vec!["a", "b"]);
    has(&grm, &firsts, "A", vec!["a"]);
    has(&grm, &firsts, "B", vec!["a"]);
    has(&grm, &firsts, "D", vec!["d", ""]);
    has(&grm, &firsts, "C", vec!["d", "a"]);
    has(&grm, &firsts, "F", vec!["d", "a"]);
}

#[test]
fn test_first_from_eco_bug() {
    let ast = parse_yacc(&"
      %start E
      %token a b c d e f
      %%
      E : T | E 'b' T;
      T : P | T 'e' P;
      P : 'a';
      C: C 'c' | ;
      D: D 'd' | F;
      F: 'f' | ;
      G: C D;
      ".to_string()).unwrap();
    let grm = ast_to_grammar(&ast);
    let firsts = Firsts::new(&grm);
    has(&grm, &firsts, "E", vec!["a"]);
    has(&grm, &firsts, "T", vec!["a"]);
    has(&grm, &firsts, "P", vec!["a"]);
    has(&grm, &firsts, "C", vec!["c", ""]);
    has(&grm, &firsts, "D", vec!["f", "d", ""]);
    has(&grm, &firsts, "G", vec!["c", "d", "f", ""]);
}

/*
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

fn grammar2() -> GrammarAST {
    let mut grm = GrammarAST::new();
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
*/

pub fn state_exists(grm: &Grammar, is: &Itemset, nt: &str, alt_off: AIdx, dot: usize, la: Vec<&str>) {
    let ab_alt_off = grm.rules_alts[grm.nonterminal_off(nt)][alt_off];
    let is = &is.items[ab_alt_off].borrow();
    if !is.active[dot] { 
        panic!("{}, alternative {}: dot {} is not active when it should be", nt, alt_off, dot);
    }
    for i in 0..grm.terms_len {
        let d = dot * grm.terms_len + i;
        let bit = is.dots[d];
        let mut found = false;
        for t in la.iter() {
            if grm.terminal_off(t) == i {
                if !bit { 
                    panic!("bit for terminal {}, dot {} is not set in alternative {} of {} when it should be", t, dot, alt_off, nt);
                }
                found = true;
                break;
            }
        }
        if !found && bit {
            panic!("bit for terminal {}, dot {} is set in alternative {} of {} when it shouldn't be", grm.terminal_names[i], dot, alt_off, nt);
        }
    }
}

#[test]
fn test_dragon_grammar() {
    // From http://binarysculpting.com/2012/02/04/computing-lr1-closure/
    let grm = ast_to_grammar(&parse_yacc(&"
      %start S
      %token e m i
      %%
      S: L 'e' R | R;
      L: 'm' R | 'i';
      R: L;
      ".to_string()).unwrap());
    let firsts = Firsts::new(&grm);

    let is = Itemset::new(&grm);
    let mut la = BitVec::from_elem(grm.terms_len, false);
    la.set(grm.terminal_off("$"), true);
    is.add(&grm, grm.rules_alts[grm.nonterminal_off("^") as usize][0], 0, &la);
    is.close(&grm, &firsts);
    state_exists(&grm, &is, "^", 0, 0, vec!["$"]);
    state_exists(&grm, &is, "S", 0, 0, vec!["$"]);
    state_exists(&grm, &is, "S", 1, 0, vec!["$"]);
    state_exists(&grm, &is, "L", 0, 0, vec!["$", "e"]);
    state_exists(&grm, &is, "L", 1, 0, vec!["$", "e"]);
    state_exists(&grm, &is, "R", 0, 0, vec!["$"]);
 }

#[test]
fn test_closure1_ecogrm() {
    let grm = eco_grammar();
    let firsts = Firsts::new(&grm);

    let mut is = Itemset::new(&grm);
    let mut la = BitVec::from_elem(grm.terms_len, false);
    la.set(grm.terminal_off("$"), true);
    is.add(&grm, grm.rules_alts[grm.nonterminal_off("^") as usize][0], 0, &la);
    is.close(&grm, &firsts);

    state_exists(&grm, &is, "^", 0, 0, vec!["$"]);
    state_exists(&grm, &is, "S", 0, 0, vec!["b", "$"]);
    state_exists(&grm, &is, "S", 1, 0, vec!["b", "$"]);
    state_exists(&grm, &is, "S", 2, 0, vec!["b", "$"]);

    is = Itemset::new(&grm);
    is.add(&grm, grm.rules_alts[grm.nonterminal_off("F") as usize][0], 0, &la);
    is.close(&grm, &firsts);
    state_exists(&grm, &is, "F", 0, 0, vec!["$"]);
    state_exists(&grm, &is, "C", 0, 0, vec!["d", "f"]);
    state_exists(&grm, &is, "D", 0, 0, vec!["a"]);
    state_exists(&grm, &is, "D", 1, 0, vec!["a"]);
}


// GrammarAST from 'LR(k) Analyse fuer Pragmatiker'
// Z : S
// S : Sb
//     bAa
// A : aSc
//     a
//     aSb
fn grammar3() -> Grammar {
    ast_to_grammar(&parse_yacc(&"
      %start S
      %token a b c d
      %%
      S: S 'b' | 'b' A 'a';
      A: 'a' S 'c' | 'a' | 'a' S 'b';
      ".to_string()).unwrap())
}

#[test]
fn test_closure1_grm3() {
    let grm = grammar3();
    let firsts = Firsts::new(&grm);

    let mut is = Itemset::new(&grm);
    let mut la = BitVec::from_elem(grm.terms_len, false);
    la.set(grm.terminal_off("$"), true);
    is.add(&grm, grm.rules_alts[grm.nonterminal_off("^") as usize][0], 0, &la);
    is.close(&grm, &firsts);

    state_exists(&grm, &is, "^", 0, 0, vec!["$"]);
    state_exists(&grm, &is, "S", 0, 0, vec!["b", "$"]);
    state_exists(&grm, &is, "S", 1, 0, vec!["b", "$"]);

    is = Itemset::new(&grm);
    la = BitVec::from_elem(grm.terms_len, false);
    la.set(grm.terminal_off("b"), true);
    la.set(grm.terminal_off("$"), true);
    is.add(&grm, grm.rules_alts[grm.nonterminal_off("S") as usize][1], 1, &la);
    is.close(&grm, &firsts);
    state_exists(&grm, &is, "A", 0, 0, vec!["a"]);
    state_exists(&grm, &is, "A", 1, 0, vec!["a"]);
    state_exists(&grm, &is, "A", 2, 0, vec!["a"]);

    is = Itemset::new(&grm);
    la = BitVec::from_elem(grm.terms_len, false);
    la.set(grm.terminal_off("a"), true);
    is.add(&grm, grm.rules_alts[grm.nonterminal_off("A") as usize][0], 1, &la);
    is.close(&grm, &firsts);
    state_exists(&grm, &is, "S", 0, 0, vec!["b", "c"]);
    state_exists(&grm, &is, "S", 1, 0, vec!["b", "c"]);
}

#[test]
fn test_goto1() {
    let grm = grammar3();
    let firsts = Firsts::new(&grm);

    let is = Itemset::new(&grm);
    let mut la = BitVec::from_elem(grm.terms_len, false);
    la.set(grm.terminal_off("$"), true);
    is.add(&grm, grm.rules_alts[grm.nonterminal_off("^") as usize][0], 0, &la);
    is.close(&grm, &firsts);

    let goto1 = is.goto(&grm, &firsts, Symbol::Nonterminal(grm.nonterminal_off("S")));
    state_exists(&grm, &goto1, "^", 0, 1, vec!["$"]);
    state_exists(&grm, &goto1, "S", 0, 1, vec!["$", "b"]);

    // follow 'b' from start set
    let goto2 = is.goto(&grm, &firsts, Symbol::Terminal(grm.terminal_off("b")));
    state_exists(&grm, &goto2, "S", 1, 1, vec!["$", "b"]);
    state_exists(&grm, &goto2, "A", 0, 0, vec!["a"]);
    state_exists(&grm, &goto2, "A", 1, 0, vec!["a"]);
    state_exists(&grm, &goto2, "A", 2, 0, vec!["a"]);

    // continue by following 'a' from last goto
    let goto3 = goto2.goto(&grm, &firsts, Symbol::Terminal(grm.terminal_off("a")));
    state_exists(&grm, &goto3, "A", 0, 1, vec!["a"]);
    state_exists(&grm, &goto3, "A", 1, 1, vec!["a"]);
    state_exists(&grm, &goto3, "A", 2, 1, vec!["a"]);
    state_exists(&grm, &goto3, "S", 0, 0, vec!["b", "c"]);
    state_exists(&grm, &goto3, "S", 1, 0, vec!["b", "c"]);
}

/*
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
*/
