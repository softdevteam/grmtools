extern crate lrpar;
use lrpar::grammar_ast::{Grammar, GrammarError, GrammarErrorKind, nonterminal, terminal};

#[test]
fn test_empty_grammar(){
    let grm = Grammar::new();
    match grm.validate() {
        Err(GrammarError{kind: GrammarErrorKind::NoStartRule, ..}) => (),
        _ => panic!("Validation error")
    }
}

#[test]
fn test_invalid_start_rule(){
    let mut grm = Grammar::new();
    grm.start = Some("A".to_string());
    grm.add_rule("B".to_string(), vec!());
    match grm.validate() {
        Err(GrammarError{kind: GrammarErrorKind::InvalidStartRule, ..}) => (),
        _ => panic!("Validation error")
    }
}

#[test]
fn test_valid_start_rule(){
    let mut grm = Grammar::new();
    grm.start = Some("A".to_string());
    grm.add_rule("A".to_string(), vec!());
    assert!(grm.validate().is_ok());
}

#[test]
fn test_valid_nonterminal_ref(){
    let mut grm = Grammar::new();
    grm.start = Some("A".to_string());
    grm.add_rule("A".to_string(), vec!(nonterminal("B")));
    grm.add_rule("B".to_string(), vec!());
    assert!(grm.validate().is_ok());
}

#[test]
fn test_invalid_nonterminal_ref(){
    let mut grm = Grammar::new();
    grm.start = Some("A".to_string());
    grm.add_rule("A".to_string(), vec!(nonterminal("B")));
    match grm.validate() {
        Err(GrammarError{kind: GrammarErrorKind::UnknownRuleRef, ..}) => (),
        _ => panic!("Validation error")
    }
}

#[test]
fn test_valid_terminal_ref(){
    let mut grm = Grammar::new();
    grm.tokens.insert("b".to_string());
    grm.start = Some("A".to_string());
    grm.add_rule("A".to_string(), vec!(terminal("b")));
    assert!(grm.validate().is_ok());
}

#[test]
fn test_invalid_terminal_ref(){
    let mut grm = Grammar::new();
    grm.start = Some("A".to_string());
    grm.add_rule("A".to_string(), vec!(terminal("b")));
    match grm.validate() {
        Err(GrammarError{kind: GrammarErrorKind::UnknownToken, ..}) => (),
        _ => panic!("Validation error")
    }
}
