use cfgrammar::yacc::{YaccKind, YaccOriginalActionKind};
use glob::glob;
use lrlex::LexerBuilder;
use lrpar::CTParserBuilder;
use std::{env, fs, path::PathBuf};
use yaml_rust::YamlLoader;

// Compiles the `*.test` files within `src`. Test files are written in Yaml syntax and have 4
// mandatory sections: name (describing what the test does), yacckind (defining the grammar type
// used), grammar (the grammar rules), and lexer (the lexing rules). The tests are compiled into
// two modules `<filename>_y` and `<filename>_l`, which we can then import into src/lib.rs and
// write tests for.
fn main() -> Result<(), Box<std::error::Error>> {
    let out_dir = env::var("OUT_DIR").unwrap();
    for entry in glob("src/*.test")? {
        let path = entry.unwrap();
        if path.is_file() {
            // Parse test file
            let s = fs::read_to_string(&path).unwrap();
            let docs = YamlLoader::load_from_str(&s).unwrap();
            let grm = &docs[0]["grammar"].as_str().unwrap();
            let lex = &docs[0]["lexer"].as_str().unwrap();
            let yacckind = match docs[0]["yacckind"].as_str().unwrap() {
                "Original(YaccOriginalActionKind::NoAction)" => {
                    YaccKind::Original(YaccOriginalActionKind::NoAction)
                }
                "Original(YaccOriginalActionKind::UserAction)" => {
                    YaccKind::Original(YaccOriginalActionKind::UserAction)
                }
                "Grmtools" => YaccKind::Grmtools,
                "Original(YaccOriginalActionKind::GenericParseTree)" => {
                    YaccKind::Original(YaccOriginalActionKind::GenericParseTree)
                }
                s => panic!("YaccKind '{}' not supported", s)
            };

            // Create grammar files
            let base = path.file_stem().unwrap().to_str().unwrap();
            let mut pg = PathBuf::from(&out_dir);
            pg.push(format!("{}.y", base));
            fs::write(&pg, &grm).unwrap();
            let mut pl = PathBuf::from(&out_dir);
            pl.push(format!("{}.l", base));
            fs::write(&pl, &lex).unwrap();

            // Build parser and lexer
            let lex_rule_ids_map = CTParserBuilder::new()
                .yacckind(yacckind)
                .process_file(pg.to_str().unwrap(), &out_dir)?;

            let mut outpl = PathBuf::from(&out_dir);
            outpl.push(format!("{}_l", base));
            outpl.set_extension("rs");
            LexerBuilder::new()
                .rule_ids_map(lex_rule_ids_map)
                .process_file(pl.to_str().unwrap(), &outpl)?;
        }
    }
    Ok(())
}
