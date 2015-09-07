extern crate bit_vec;
use self::bit_vec::BitVec;

extern crate lrpar;
use lrpar::grammar::{AIdx, ast_to_grammar, Grammar, Symbol};
use lrpar::yacc::parse_yacc;
use lrpar::pgen::{Itemset, Firsts, StateGraph};

fn has(grm: &Grammar, firsts: &Firsts, rn: &str, should_be: Vec<&str>) {
    let nt_i = grm.nonterminal_off(rn);
    for (i, n) in grm.terminal_names.iter().enumerate() {
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

pub fn state_exists(grm: &Grammar, is: &Itemset, nt: &str, alt_off: AIdx, dot: usize, la:
                    Vec<&str>) {
    let ab_alt_off = grm.rules_alts[grm.nonterminal_off(nt)][alt_off];
    let item_rc = &is.items[ab_alt_off].borrow();
    if item_rc.as_ref().is_none() {
        panic!("{}, alternative {} is not allocated when it should be", nt, alt_off);
    }
    let lookahead_opt = &item_rc.as_ref().unwrap().lookaheads[dot].borrow();
    if lookahead_opt.is_none() {
        panic!("{}, alternative {}: dot {} is not active when it should be", nt, alt_off, dot);
    }
    let lookahead = &lookahead_opt.as_ref().unwrap();
    for i in 0..grm.terms_len {
        let bit = lookahead[i];
        let mut found = false;
        for t in la.iter() {
            if grm.terminal_off(t) == i {
                if !bit {
                    panic!("bit for terminal {}, dot {} is not set in alternative {} of {} when it should be",
                           t, dot, alt_off, nt);
                }
                found = true;
                break;
            }
        }
        if !found && bit {
            panic!("bit for terminal {}, dot {} is set in alternative {} of {} when it shouldn't be",
                   grm.terminal_names[i], dot, alt_off, nt);
        }
    }
}

pub fn num_active_states(is: &Itemset) -> usize {
    let mut a = 0;
    for item_rc in is.items.iter() {
        let item_opt = item_rc.borrow();
        if item_opt.is_none() { continue; }
        a += item_opt.as_ref().unwrap().lookaheads.iter().fold(0, |acc, ref la_opt|
                                                                  if la_opt.borrow().is_some() {
                                                                      acc + 1 
                                                                  } else { acc });
    }
    a
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
    assert_eq!(num_active_states(&is), 6);
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

#[test]
fn test_stategraph() {
    let grm = grammar3();
    let sg = StateGraph::new(&grm);
    for st in sg.states.iter() { println!("  {:?}", st); }

    assert_eq!(sg.states.len(), 13);
    assert_eq!(sg.edges.len(), 13);

    assert_eq!(num_active_states(&sg.states[0]), 3);
    state_exists(&grm, &sg.states[0], "^", 0, 0, vec!["$"]);
    state_exists(&grm, &sg.states[0], "S", 0, 0, vec!["$", "b"]);
    state_exists(&grm, &sg.states[0], "S", 1, 0, vec!["$", "b"]);

    let s1 = sg.edges[&(0, Symbol::Nonterminal(grm.nonterminal_off("S")))];
    assert_eq!(num_active_states(&sg.states[s1]), 2);
    state_exists(&grm, &sg.states[s1], "^", 0, 1, vec!["$"]);
    state_exists(&grm, &sg.states[s1], "S", 0, 1, vec!["$", "b"]);

    let s2 = sg.edges[&(s1, Symbol::Terminal(grm.terminal_off("b")))];
    assert_eq!(num_active_states(&sg.states[s2]), 1);
    state_exists(&grm, &sg.states[s2], "S", 0, 2, vec!["$", "b"]);

    let s3 = sg.edges[&(0, Symbol::Terminal(grm.terminal_off("b")))];
    assert_eq!(num_active_states(&sg.states[s3]), 4);
    state_exists(&grm, &sg.states[s3], "S", 1, 1, vec!["$", "b"]);
    state_exists(&grm, &sg.states[s3], "A", 0, 0, vec!["a"]);
    state_exists(&grm, &sg.states[s3], "A", 1, 0, vec!["a"]);
    state_exists(&grm, &sg.states[s3], "A", 2, 0, vec!["a"]);

    let s4 = sg.edges[&(s3, Symbol::Nonterminal(grm.nonterminal_off("A")))];
    assert_eq!(num_active_states(&sg.states[s4]), 1);
    state_exists(&grm, &sg.states[s4], "S", 1, 2, vec!["$", "b"]);

    let s5 = sg.edges[&(s4, Symbol::Terminal(grm.terminal_off("a")))];
    assert_eq!(num_active_states(&sg.states[s5]), 1);
    state_exists(&grm, &sg.states[s5], "S", 1, 3, vec!["$", "b"]);

    let s6 = sg.edges[&(s3, Symbol::Terminal(grm.terminal_off("a")))];
    assert_eq!(num_active_states(&sg.states[s6]), 5);
    state_exists(&grm, &sg.states[s6], "A", 0, 1, vec!["a"]);
    state_exists(&grm, &sg.states[s6], "A", 1, 1, vec!["a"]);
    state_exists(&grm, &sg.states[s6], "A", 2, 1, vec!["a"]);
    state_exists(&grm, &sg.states[s6], "S", 0, 0, vec!["b", "c"]);
    state_exists(&grm, &sg.states[s6], "S", 1, 0, vec!["b", "c"]);

    let s7 = sg.edges[&(s6, Symbol::Nonterminal(grm.nonterminal_off("S")))];
    assert_eq!(num_active_states(&sg.states[s7]), 3);
    state_exists(&grm, &sg.states[s7], "A", 0, 2, vec!["a"]);
    state_exists(&grm, &sg.states[s7], "A", 2, 2, vec!["a"]);
    state_exists(&grm, &sg.states[s7], "S", 0, 1, vec!["b", "c"]);

    let s8 = sg.edges[&(s7, Symbol::Terminal(grm.terminal_off("c")))];
    assert_eq!(num_active_states(&sg.states[s8]), 1);
    state_exists(&grm, &sg.states[s8], "A", 0, 3, vec!["a"]);

    let s9 = sg.edges[&(s7, Symbol::Terminal(grm.terminal_off("b")))];
    assert_eq!(num_active_states(&sg.states[s9]), 2);
    state_exists(&grm, &sg.states[s9], "A", 2, 3, vec!["a"]);
    state_exists(&grm, &sg.states[s9], "S", 0, 2, vec!["b", "c"]);

    let s10 = sg.edges[&(s6, Symbol::Terminal(grm.terminal_off("b")))];
    assert_eq!(s6, sg.edges[&(s10, Symbol::Terminal(grm.terminal_off("a")))]);
    assert_eq!(num_active_states(&sg.states[s10]), 4);
    state_exists(&grm, &sg.states[s10], "S", 1, 1, vec!["b", "c"]);
    state_exists(&grm, &sg.states[s10], "A", 0, 0, vec!["a"]);
    state_exists(&grm, &sg.states[s10], "A", 1, 0, vec!["a"]);
    state_exists(&grm, &sg.states[s10], "A", 2, 0, vec!["a"]);

    let s11 = sg.edges[&(s10, Symbol::Nonterminal(grm.nonterminal_off("A")))];
    assert_eq!(num_active_states(&sg.states[s11]), 1);
    state_exists(&grm, &sg.states[s11], "S", 1, 2, vec!["b", "c"]);

    let s12 = sg.edges[&(s11, Symbol::Terminal(grm.terminal_off("a")))];
    assert_eq!(num_active_states(&sg.states[s12]), 1);
    state_exists(&grm, &sg.states[s12], "S", 1, 3, vec!["b", "c"]);
}

