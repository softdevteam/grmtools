use lrlex::LexerBuilder;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Note that we specify the integer type (u8) we'll use for token IDs (this type *must* be big
    // enough to fit all IDs in) as well as the input file (which must end in ".l").
    LexerBuilder::<u8>::new()
        .lexer_in_src_dir("calc.l")?
        .process()?;
    Ok(())
}
