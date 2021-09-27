use lrlex::CTLexerBuilder;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    CTLexerBuilder::new().lexer_in_src_dir("calc.l")?.build()?;
    Ok(())
}
