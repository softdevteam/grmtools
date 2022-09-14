 mod erroneous_l {
use lrlex::{LexerDef, LRNonStreamingLexerDef, Rule, StartState};

#[allow(dead_code)]
pub fn lexerdef() -> LRNonStreamingLexerDef<lrlex::lexemes::DefaultLexeme, u32> {
    let start_states: Vec<StartState> = vec![
        StartState::new(0, "INITIAL", false, ::cfgrammar::Span::new(0, 0)),
    ];
    let rules = vec![
        Rule::new(Some(0), Some("a".to_string()), ::cfgrammar::Span::new(6, 7), "a".to_string(), [].to_vec(), None).unwrap(),
        Rule::new(Some(1), Some("b".to_string()), ::cfgrammar::Span::new(12, 13), "b".to_string(), [].to_vec(), None).unwrap(),
        Rule::new(Some(2), None, ::cfgrammar::Span::new(17, 17), ".".to_string(), [].to_vec(), None).unwrap(),
    ];
    LRNonStreamingLexerDef::from_rules(start_states, rules)
}

}