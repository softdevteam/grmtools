use cfgrammar::yacc::{YaccKind, YaccOriginalActionKind};
use lrlex::CTLexerBuilder;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Since we're using both lrlex and lrpar, we use lrlex's `lrpar_config` convenience function
    // that makes it easy to a) create a lexer and parser and b) link them together.
    //
    // Note that we specify the integer type (u8) we'll use for token IDs (this type *must* be big
    // enough to fit all IDs in) as well as the input file (which must end in ".y" for lrpar, and
    // ".l" for lrlex).
    CTLexerBuilder::<u8>::new_with_storaget()
        .lrpar_config(|ctp| {
            ctp.yacckind(YaccKind::Original(YaccOriginalActionKind::GenericParseTree))
                .grammar_in_src_dir("calc.y")
                .unwrap()
        })
        .lexer_in_src_dir("calc.l")?
        .build()?;
    Ok(())
}
