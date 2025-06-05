use lrlex::{CTTokenMapBuilder, DefaultLexerTypes};
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
    CTTokenMapBuilder::<u8>::new("token_map", ctp.token_map())
        .rename_map(Some(TOKENS_MAP))
        .build()
        .unwrap();
}
