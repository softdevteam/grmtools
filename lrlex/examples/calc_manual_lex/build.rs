use cfgrammar::yacc::YaccKind;
use lrlex::{ct_token_map, DefaultLexerTypes};
use lrpar::CTParserBuilder;

// Some of the token names in the parser do not lead to valid Rust identifiers, so we map them to
// valid identifier names here.
const TOKENS_MAP: &[(&str, &str)] = &[
    ("+", "PLUS"),
    ("*", "STAR"),
    ("(", "LBRACK"),
    (")", "RBRACK"),
];

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let ctp = CTParserBuilder::<DefaultLexerTypes<u8>>::new()
        .yacckind(YaccKind::Grmtools)
        .grammar_in_src_dir("calc.y")?
        .build()?;
    ct_token_map::<u8>(
        "token_map",
        ctp.token_map(),
        Some(&TOKENS_MAP.iter().cloned().collect()),
    )
}
