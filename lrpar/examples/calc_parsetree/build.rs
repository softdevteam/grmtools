use cfgrammar::yacc::{YaccKind, YaccOriginalActionKind};
use lrlex::CTLexerBuilder;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Since we're using both lrlex and lrpar, we use lrlex's `lrpar_config` convenience function
    // that makes it easy to a) create a lexer and parser and b) link them together.
    CTLexerBuilder::new()
        .rust_edition(lrlex::RustEdition::Rust2021)
        .lrpar_config(|ctp| {
            ctp.yacckind(YaccKind::Original(YaccOriginalActionKind::GenericParseTree))
                .rust_edition(lrpar::RustEdition::Rust2021)
                .grammar_in_src_dir("calc.y")
                .unwrap()
        })
        .lexer_in_src_dir("calc.l")?
        .build()?;
    Ok(())
}
