use cfgrammar::yacc::YaccKind;
use lrlex::LexerBuilder;
use lrpar::CTParserBuilder;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // First we create the parser, which returns a HashMap of all the tokens used, then we pass
    // that HashMap to the lexer.
    //
    // Note that we specify the integer type (u8) we'll use for token IDs (this type *must* be big
    // enough to fit all IDs in) as well as the input file (which must end in ".y" for lrpar, and
    // ".l" for lrlex).
    let cp = CTParserBuilder::new()
        .yacckind(YaccKind::Grmtools)
        .grammar_in_src_dir("calc.y")?
        .build()?;
    LexerBuilder::new()
        .rule_ids_map(cp.lexeme_id_map())
        .lexer_in_src_dir("calc.l")?
        .process()?;
    Ok(())
}
