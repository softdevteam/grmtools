use glob::glob;
#[path = "src/cgen_helper.rs"]
mod cgen_helper;
use cfg_aliases::cfg_aliases;
use cgen_helper::run_test_path;

// Compiles the `*.test` files within `src`. Test files are written in Yaml syntax and have 4
// mandatory sections: name (describing what the test does), yacckind (defining the grammar type
// used), grammar (the grammar rules), and lexer (the lexing rules). The tests are compiled into
// two modules `<filename>_y` and `<filename>_l`, which we can then import into src/lib.rs and
// write tests for.
fn main() -> Result<(), Box<dyn std::error::Error>> {
    for entry in glob("src/*.test")? {
        run_test_path(entry.unwrap())?;
    }

    cfg_aliases! {
        // Platforms
        wasm32_unknown: { all(target_arch = "wasm32", target_os="unknown", target_vendor="unknown") },
    }

    Ok(())
}
