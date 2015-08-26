extern crate lrpar;
use lrpar::grammar::{Grammar, GrammarError, GrammarErrorKind, nonterminal, terminal};

#[test]
fn test_empty_grammar(){
    let grm = Grammar::new();
    match grm.validate() {
        Err(GrammarError{kind: GrammarErrorKind::InvalidStartRule, ..}) => (),
        _ => panic!("Validation error")
    }
}

#[test]
fn test_invalid_start_rule(){
    let mut grm = Grammar::new();
    grm.start = "A".to_string();
    grm.add_rule("B".to_string(), vec!());
    match grm.validate() {
        Err(GrammarError{kind: GrammarErrorKind::InvalidStartRule, ..}) => (),
        _ => panic!("Validation error")
    }
}

#[test]
fn test_valid_start_rule(){
    let mut grm = Grammar::new();
    grm.start = "A".to_string();
    grm.add_rule("A".to_string(), vec!());
    assert!(grm.validate().is_ok());
}

#[test]
fn test_valid_nonterminal_ref(){
    let mut grm = Grammar::new();
    grm.start = "A".to_string();
    grm.add_rule("A".to_string(), vec!(nonterminal("B")));
    grm.add_rule("B".to_string(), vec!());
    assert!(grm.validate().is_ok());
}

#[test]
fn test_invalid_nonterminal_ref(){
    let mut grm = Grammar::new();
    grm.start = "A".to_string();
    grm.add_rule("A".to_string(), vec!(nonterminal("B")));
    match grm.validate() {
        Err(GrammarError{kind: GrammarErrorKind::UnknownRuleRef, ..}) => (),
        _ => panic!("Validation error")
    }
}

#[test]
#[should_panic]
fn test_valid_token_ref(){
    // for now we won't support the YACC feature that allows
    // to redefine nonterminals as tokens by adding them to '%token'
    let mut grm = Grammar::new();
    grm.tokens.insert("b".to_string());
    grm.start = "A".to_string();
    grm.add_rule("A".to_string(), vec!(nonterminal("b")));
    assert!(grm.validate().is_ok());
}

#[test]
fn test_invalid_nonterminal_forgotten_token(){
    let mut grm = Grammar::new();
    grm.start = "A".to_string();
    grm.add_rule("A".to_string(), vec!(nonterminal("b"), terminal("b")));
    match grm.validate() {
        Err(GrammarError{kind: GrammarErrorKind::UnknownRuleRef, ..}) => (),
        _ => panic!("Validation error")
    }
}
