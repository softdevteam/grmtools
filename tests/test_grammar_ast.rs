extern crate lrpar;
use lrpar::grammar_ast::{GrammarAST, GrammarASTError, GrammarASTErrorKind, nonterminal, terminal};

#[test]
fn test_empty_grammar(){
    let grm = GrammarAST::new();
    match grm.validate() {
        Err(GrammarASTError{kind: GrammarASTErrorKind::NoStartRule, ..}) => (),
        _ => panic!("Validation error")
    }
}

#[test]
fn test_invalid_start_rule(){
    let mut grm = GrammarAST::new();
    grm.start = Some("A".to_string());
    grm.add_rule("B".to_string(), vec!());
    match grm.validate() {
        Err(GrammarASTError{kind: GrammarASTErrorKind::InvalidStartRule, ..}) => (),
        _ => panic!("Validation error")
    }
}

#[test]
fn test_valid_start_rule(){
    let mut grm = GrammarAST::new();
    grm.start = Some("A".to_string());
    grm.add_rule("A".to_string(), vec!());
    assert!(grm.validate().is_ok());
}

#[test]
fn test_valid_nonterminal_ref(){
    let mut grm = GrammarAST::new();
    grm.start = Some("A".to_string());
    grm.add_rule("A".to_string(), vec!(nonterminal("B")));
    grm.add_rule("B".to_string(), vec!());
    assert!(grm.validate().is_ok());
}

#[test]
fn test_invalid_nonterminal_ref(){
    let mut grm = GrammarAST::new();
    grm.start = Some("A".to_string());
    grm.add_rule("A".to_string(), vec!(nonterminal("B")));
    match grm.validate() {
        Err(GrammarASTError{kind: GrammarASTErrorKind::UnknownRuleRef, ..}) => (),
        _ => panic!("Validation error")
    }
}

#[test]
fn test_valid_terminal_ref(){
    let mut grm = GrammarAST::new();
    grm.tokens.insert("b".to_string());
    grm.start = Some("A".to_string());
    grm.add_rule("A".to_string(), vec!(terminal("b")));
    assert!(grm.validate().is_ok());
}

#[test]
#[should_panic]
fn test_valid_token_ref(){
    // for now we won't support the YACC feature that allows
    // to redefine nonterminals as tokens by adding them to '%token'
    let mut grm = GrammarAST::new();
    grm.tokens.insert("b".to_string());
    grm.start = Some("A".to_string());
    grm.add_rule("A".to_string(), vec!(nonterminal("b")));
    assert!(grm.validate().is_ok());
}

#[test]
fn test_invalid_terminal_ref(){
    let mut grm = GrammarAST::new();
    grm.start = Some("A".to_string());
    grm.add_rule("A".to_string(), vec!(terminal("b")));
    match grm.validate() {
        Err(GrammarASTError{kind: GrammarASTErrorKind::UnknownToken, ..}) => (),
        _ => panic!("Validation error")
    }
}

#[test]
fn test_invalid_nonterminal_forgotten_token(){
    let mut grm = GrammarAST::new();
    grm.start = Some("A".to_string());
    grm.add_rule("A".to_string(), vec!(nonterminal("b"), terminal("b")));
    match grm.validate() {
        Err(GrammarASTError{kind: GrammarASTErrorKind::UnknownRuleRef, ..}) => (),
        _ => panic!("Validation error")
    }
}
