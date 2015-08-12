extern crate lrpar;
use lrpar::{YaccError, YaccErrorKind};
use lrpar::grammar::{Rule, Symbol, SymbolType};
use lrpar::yacc::parse_yacc;

macro_rules! terminal {
    ($x:expr) => (Symbol::new($x.to_string(), SymbolType::Terminal));
}
macro_rules! nonterminal {
    ($x:expr) => (Symbol::new($x.to_string(), SymbolType::Nonterminal));
}

#[test]
fn test_macro() {
    assert_eq!(Symbol::new("A".to_string(), SymbolType::Terminal), terminal!("A"));
}

#[test]
fn test_symbol_eq() {
    assert_eq!(Symbol::new("A".to_string(), SymbolType::Nonterminal),
      Symbol::new("A".to_string(), SymbolType::Nonterminal));
    assert!(Symbol::new("A".to_string(), SymbolType::Terminal)
      != Symbol::new("B".to_string(), SymbolType::Terminal));
    assert!(Symbol::new("A".to_string(), SymbolType::Terminal)
      != Symbol::new("A".to_string(), SymbolType::Nonterminal));
}

#[test]
fn test_rule_eq() {
    assert_eq!(Rule::new("A".to_string()), Rule::new("A".to_string()));
    assert!(Rule::new("A".to_string()) != Rule::new("B".to_string()));

    let mut rule1 = Rule::new("A".to_string());
    rule1.add_symbols(vec![terminal!("a")]);
    let mut rule2 = Rule::new("A".to_string());
    rule2.add_symbols(vec![terminal!("a")]);
    assert_eq!(rule1, rule2);
}

#[test]
fn test_rule() {
    let src = "
        %%
        A : 'a';
    ".to_string();
    let grm = parse_yacc(&src).unwrap();
    let mut rule1 = Rule::new("A".to_string());
    rule1.add_symbols(vec![terminal!("a")]);
    assert_eq!(*grm.get_rule("A").unwrap(), rule1);
    let mut rule2 = Rule::new("B".to_string());
    rule2.add_symbols(vec![terminal!("a")]);
    assert!(*grm.get_rule("A").unwrap() != rule2);
}

#[test]
fn test_rule_alternative_simple() {
    let src = "
        %%
        A : 'a';
        A : 'b';
    ".to_string();
    let grm = parse_yacc(&src).unwrap();
    let mut rule1 = Rule::new("A".to_string());
    rule1.add_symbols(vec![terminal!("a")]);
    rule1.add_symbols(vec![terminal!("b")]);
    assert_eq!(*grm.get_rule("A").unwrap(), rule1);
    let mut rule2 = Rule::new("B".to_string());
    rule2.add_symbols(vec![terminal!("a")]);
    assert!(*grm.get_rule("A").unwrap() != rule2);
}


#[test]
fn test_rule_empty() {
    let src = "
        %%
        A : ;
        B : 'b' | ;
        C : | 'c';
    ".to_string();
    let grm = parse_yacc(&src).unwrap();

    let mut rule1 = Rule::new("A".to_string());
    rule1.add_symbols(vec![]);
    assert_eq!(*grm.get_rule("A").unwrap(), rule1);

    let mut rule2 = Rule::new("B".to_string());
    rule2.add_symbols(vec![terminal!("b")]);
    rule2.add_symbols(vec![]);
    assert_eq!(*grm.get_rule("B").unwrap(), rule2);

    let mut rule3 = Rule::new("C".to_string());
    rule3.add_symbols(vec![]);
    rule3.add_symbols(vec![terminal!("c")]);
    assert_eq!(*grm.get_rule("C").unwrap(), rule3);
}

#[test]
fn test_rule_alternative_verticalbar() {
    let src = "
        %%
        A : 'a' | 'b';
    ".to_string();
    let grm = parse_yacc(&src).unwrap();
    let mut rule1 = Rule::new("A".to_string());
    rule1.add_symbols(vec![terminal!("a")]);
    rule1.add_symbols(vec![terminal!("b")]);
    assert_eq!(*grm.get_rule("A").unwrap(), rule1);
    let mut rule2 = Rule::new("B".to_string());
    rule2.add_symbols(vec![terminal!("a")]);
    assert!(*grm.get_rule("A").unwrap() != rule2);
}

#[test]
fn test_empty_program() {
    let src = "%%\nA : 'a';\n%%".to_string();
    parse_yacc(&src).unwrap();
}

#[test]
fn test_multiple_symbols() {
    let src = "%%\nA : 'a' B;".to_string();
    let grm = parse_yacc(&src).unwrap();
    let mut rule = Rule::new("A".to_string());
    rule.add_symbols(vec![terminal!("a"), nonterminal!("B")]);
    assert_eq!(*grm.get_rule("A").unwrap(), rule)
}

#[test]
fn test_token_types() {
    let src = "%%\nA : 'a' \"b\";".to_string();
    let grm = parse_yacc(&src).unwrap();
    let mut rule = Rule::new("A".to_string());
    rule.add_symbols(vec![terminal!("a"), terminal!("b")]);
    assert_eq!(*grm.get_rule("A").unwrap(), rule)
}

#[test]
fn test_declaration_start() {
    let src = "%start   A\n%%\nA : a;".to_string();
    let grm = parse_yacc(&src).unwrap();
    assert_eq!(grm.get_start(), "A");
}

#[test]
fn test_declaration_token() {
    let src = "%token   a\n%%\nA : a;".to_string();
    let grm = parse_yacc(&src).unwrap();
    assert!(grm.has_token("a"));
}

#[test]
fn test_declaration_tokens() {
    let src = "%token   a b c\n%%\nA : a;".to_string();
    let grm = parse_yacc(&src).unwrap();
    assert!(grm.has_token("a"));
    assert!(grm.has_token("b"));
    assert!(grm.has_token("c"));
}

#[test]
#[should_panic]
fn test_simple_decl_fail() {
    let src = "%fail x\n%%\nA : a".to_string();
    parse_yacc(&src).unwrap();
}

#[test]
#[should_panic]
fn test_empty() {
    let src = "".to_string();
    parse_yacc(&src).unwrap();
}

#[test]
fn test_illegal_name() {
    let src = "%%0:A;".to_string();
    match parse_yacc(&src) {
        Ok(_)  => panic!("Illegal name parsed"),
        Err(YaccError{kind: YaccErrorKind::IllegalName, ..}) => (),
        Err(_) => panic!("Incorrect error returned")
    }
}

#[test]
fn test_illegal_string() {
    let src = "%%A:' ';".to_string();
    match parse_yacc(&src) {
        Ok(_)  => panic!("Illegal string parsed"),
        Err(YaccError{kind: YaccErrorKind::IllegalString, ..}) => (),
        Err(e) => panic!("Incorrect error returned {}", e)
    }
}

#[test]
fn test_incomplete_rule1() {
    let src = "%%A:".to_string();
    match parse_yacc(&src) {
        Ok(_)  => panic!("Incomplete rule parsed"),
        Err(YaccError{kind: YaccErrorKind::IncompleteRule, ..}) => (),
        Err(e) => panic!("Incorrect error returned {}", e)
    }
}

#[test]
fn test_missing_colon() {
    let src = "%%A x;".to_string();
    match parse_yacc(&src) {
        Ok(_)  => panic!("Missing colon parsed"),
        Err(YaccError{kind: YaccErrorKind::MissingColon, ..}) => (),
        Err(e) => panic!("Incorrect error returned {}", e)
    }
}

#[test]
fn test_premature_end() {
    let src = "%token x".to_string();
    match parse_yacc(&src) {
        Ok(_)  => panic!("Incomplete rule parsed"),
        Err(YaccError{kind: YaccErrorKind::PrematureEnd, ..}) => (),
        Err(e) => panic!("Incorrect error returned {}", e)
    }
}

#[test]
fn test_programs_not_supported() {
    let src = "%% %% x".to_string();
    match parse_yacc(&src) {
        Ok(_)  => panic!("Programs parsed"),
        Err(YaccError{kind: YaccErrorKind::ProgramsNotSupported, ..}) => (),
        Err(e) => panic!("Incorrect error returned {}", e)
    }
}

#[test]
fn test_unknown_declaration() {
    let src = "%woo".to_string();
    match parse_yacc(&src) {
        Ok(_)  => panic!("Unknown declaration parsed"),
        Err(YaccError{kind: YaccErrorKind::UnknownDeclaration, ..}) => (),
        Err(e) => panic!("Incorrect error returned {}", e)
    }
}
