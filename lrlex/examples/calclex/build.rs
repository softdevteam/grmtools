use lrlex::CTLexerBuilder;

fn main() {
    CTLexerBuilder::new()
        .lexer_in_src_dir("calc.l")
        .unwrap()
        .build()
        .unwrap();
}
