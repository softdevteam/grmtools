extern crate lrpar;

use lrpar::grammar::{ast_to_grammar, Symbol};
use lrpar::yacc::parse_yacc;

#[test]
fn test_minimal() {
    let ast = parse_yacc(&"%start R %token T %% R: 'T';".to_string()).unwrap();
    let grm = ast_to_grammar(&ast);

    assert_eq!(grm.start_alt, 0);
    grm.nonterminal_off("^");
    grm.nonterminal_off("R");
    grm.terminal_off("$");
    grm.terminal_off("T");

    assert_eq!(grm.rules_alts, vec![vec![0], vec![1]]);
    let start_alt = grm.alts.get(grm.rules_alts.get(grm.nonterminal_off("^")).unwrap()[0]).unwrap();
    assert_eq!(*start_alt, vec![Symbol::Nonterminal(grm.nonterminal_off("R"))]);
    let r_alt = grm.alts.get(grm.rules_alts.get(grm.nonterminal_off("R")).unwrap()[0] as
                             usize).unwrap();
    assert_eq!(*r_alt, vec![Symbol::Terminal(grm.terminal_off("T"))]);
}

#[test]
fn test_rule_ref() {
    let ast = parse_yacc(&"%start R %token T %% R : S; S: 'T';".to_string()).unwrap();
    let grm = ast_to_grammar(&ast);

    grm.nonterminal_off("^");
    grm.nonterminal_off("R");
    grm.nonterminal_off("S");
    grm.terminal_off("$");
    grm.terminal_off("T");

    assert_eq!(grm.rules_alts, vec![vec![0], vec![1], vec![2]]);
    let start_alt = grm.alts.get(grm.rules_alts.get(grm.nonterminal_off("^")).unwrap()[0]).unwrap();
    assert_eq!(*start_alt, vec![Symbol::Nonterminal(grm.nonterminal_off("R"))]);
    let r_alt = grm.alts.get(grm.rules_alts.get(grm.nonterminal_off("R")).unwrap()[0] as
                             usize).unwrap();
    assert_eq!(r_alt.len(), 1);
    assert_eq!(r_alt[0], Symbol::Nonterminal(grm.nonterminal_off("S")));
    let s_alt = grm.alts.get(grm.rules_alts.get(grm.nonterminal_off("S")).unwrap()[0] as
                             usize).unwrap();
    assert_eq!(s_alt.len(), 1);
    assert_eq!(s_alt[0], Symbol::Terminal(grm.terminal_off("T")));
}

#[test]
fn test_long_alt() {
    let ast = parse_yacc(&"%start R %token T1 T2 %% R : S 'T1' S; S: 'T2';".to_string()).unwrap();
    let grm = ast_to_grammar(&ast);

    grm.nonterminal_off("^");
    grm.nonterminal_off("R");
    grm.nonterminal_off("S");
    grm.terminal_off("$");
    grm.terminal_off("T1");
    grm.terminal_off("T2");

    assert_eq!(grm.rules_alts, vec![vec![0], vec![1], vec![2]]);
    let start_alt = grm.alts.get(grm.rules_alts.get(grm.nonterminal_off("^")).unwrap()[0]).unwrap();
    assert_eq!(*start_alt, vec![Symbol::Nonterminal(grm.nonterminal_off("R"))]);
    let r_alt = grm.alts.get(grm.rules_alts.get(grm.nonterminal_off("R")).unwrap()[0] as
                             usize).unwrap();
    assert_eq!(r_alt.len(), 3);
    assert_eq!(r_alt[0], Symbol::Nonterminal(grm.nonterminal_off("S")));
    assert_eq!(r_alt[1], Symbol::Terminal(grm.terminal_off("T1")));
    assert_eq!(r_alt[2], Symbol::Nonterminal(grm.nonterminal_off("S")));
    let s_alt = grm.alts.get(grm.rules_alts.get(grm.nonterminal_off("S")).unwrap()[0] as
                             usize).unwrap();
    assert_eq!(s_alt.len(), 1);
    assert_eq!(s_alt[0], Symbol::Terminal(grm.terminal_off("T2")));
}
