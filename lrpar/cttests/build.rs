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
