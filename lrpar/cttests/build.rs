use cfgrammar::yacc::ast::ASTWithValidityInfo;
use glob::glob;
#[path = "src/cgen_helper.rs"]
mod cgen_helper;
use cfg_aliases::cfg_aliases;
use cgen_helper::run_test_path;
use lrlex::{CTLexerBuilder, DefaultLexerTypes};

// Compiles the `*.test` files within `src`. Test files are written in Yaml syntax and have 4
// mandatory sections: name (describing what the test does), yacckind (defining the grammar type
// used), grammar (the grammar rules), and lexer (the lexing rules). The tests are compiled into
// two modules `<filename>_y` and `<filename>_l`, which we can then import into src/lib.rs and
// write tests for.
fn main() -> Result<(), Box<dyn std::error::Error>> {
    for src in glob("src/*.rs")? {
        println!("cargo::rerun-if-changed={}", src?.display());
    }
    for entry in glob("src/*.test")? {
        run_test_path(entry.unwrap())?;
    }

    cfg_aliases! {
        // Platforms
        wasm32_unknown: { all(target_arch = "wasm32", target_os="unknown", target_vendor="unknown") },
    }

    {
        // Because we're modifying the `StorageT` this isn't something `run_test_path` can do,
        // Since it modifies the type of the builder.
        CTLexerBuilder::<DefaultLexerTypes<u8>>::new_with_lexemet()
            .rust_edition(lrlex::RustEdition::Rust2021)
            .output_path(format!(
                "{}/storaget.l.rs",
                std::env::var("OUT_DIR").unwrap()
            ))
            .lrpar_config(|ctp| {
                ctp.rust_edition(lrpar::RustEdition::Rust2021)
                    .output_path(format!(
                        "{}/storaget.y.rs",
                        std::env::var("OUT_DIR").unwrap()
                    ))
                    .grammar_in_src_dir("storaget.y")
                    .unwrap()
            })
            .lexer_in_src_dir("storaget.l")
            .unwrap()
            .build()
            .unwrap();
    }

    {
        use lrpar::unstable_api::UnstableApi;
        // In this case we'll be building multiple grammars
        //
        // 1. Parse multi_start_rule.y into an AST
        // 2. Clone the original and change the start rule.
        // 3. Build a grammar for `multi_start_rule.y` unchanged.
        // 4. Build the modified grammar.
        let grammar_path = &std::env::current_dir().unwrap().join("src/multi_start.y");
        let grammar_src = std::fs::read_to_string(grammar_path).unwrap();
        let grammar_src_clone = grammar_src.clone();
        let valid_ast = ASTWithValidityInfo::new(cfgrammar::yacc::YaccKind::Grmtools, &grammar_src);
        eprintln!("rules {:?}", valid_ast.ast().rules);
        let bstart_rule = valid_ast.ast().get_rule("BStart").unwrap().clone();
        let modified_ast = valid_ast.clone_and_change_start_rule(bstart_rule).unwrap();
        CTLexerBuilder::new()
            .lrpar_config(move |ctp| {
                ctp.grammar_ast(valid_ast.clone(), UnstableApi)
                    .with_grammar_src(grammar_src.clone(), UnstableApi)
                    .grammar_in_src_dir("multi_start.y")
                    .unwrap()
                    .mod_name("ast_unmodified_y")
                    .output_path(format!(
                        "{}/ast_unmodified.y.rs",
                        std::env::var("OUT_DIR").unwrap()
                    ))
            })
            .lexer_in_src_dir("multi_start.l")
            .unwrap()
            .output_path(format!(
                "{}/ast_unmodified.l.rs",
                std::env::var("OUT_DIR").unwrap()
            ))
            .mod_name("ast_unmodified_l")
            .build()
            .unwrap();
        CTLexerBuilder::new()
            .lrpar_config(move |ctp| {
                ctp.grammar_ast(modified_ast.clone(), UnstableApi)
                    .with_grammar_src(grammar_src_clone.clone(), UnstableApi)
                    .grammar_in_src_dir("multi_start.y")
                    .unwrap()
                    .mod_name("ast_modified_y")
                    .output_path(format!(
                        "{}/ast_modified.y.rs",
                        std::env::var("OUT_DIR").unwrap()
                    ))
                    // We still need to disable these because they are checked after ast validation.
                    .warnings_are_errors(false)
                    .show_warnings(false)
            })
            .lexer_in_src_dir("multi_start.l")
            .unwrap()
            .mod_name("ast_modified_l")
            .output_path(format!(
                "{}/ast_modified.l.rs",
                std::env::var("OUT_DIR").unwrap()
            ))
            .build()
            .unwrap();
    }
    println!("cargo::rerun-if-changed=src/storaget.l");
    println!(
        "cargo::rerun-if-changed={}/storaget.l.rs",
        std::env::var("OUT_DIR").unwrap()
    );
    println!("cargo::rerun-if-changed=src/storaget.y");
    println!(
        "cargo::rerun-if-changed={}/storaget.y.rs",
        std::env::var("OUT_DIR").unwrap()
    );
    Ok(())
}
