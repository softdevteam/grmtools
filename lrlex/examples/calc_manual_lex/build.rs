use lrlex::{DefaultLexerTypes, ct_token_map};
use lrpar::CTParserBuilder;

// Some of the token names in the parser do not lead to valid Rust identifiers, so we map them to
// valid identifier names here.
const TOKENS_MAP: &[(&str, &str)] = &[
    ("+", "PLUS"),
    ("*", "STAR"),
    ("(", "LBRACK"),
    (")", "RBRACK"),
];

fn main() {
    let ctp = CTParserBuilder::<DefaultLexerTypes<u8>>::new()
        .grammar_in_src_dir("calc.y")
        .unwrap()
        .build()
        .unwrap();
    ct_token_map::<u8>(
        "token_map",
        ctp.token_map(),
        Some(&TOKENS_MAP.iter().cloned().collect()),
    )
    .unwrap();
}
