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
        use lrpar::RecoveryKind as RK;
        #[rustfmt::skip]
        let recovery_kinds = vec![
            //  Builder,          Header setting,     Expected result.
            // -----------       ------------------  -------------------
            (Some(RK::None),      Some(RK::None),     Some(RK::None)),
            (Some(RK::None),      Some(RK::CPCTPlus), Some(RK::None)),
            (Some(RK::CPCTPlus),  Some(RK::CPCTPlus), Some(RK::CPCTPlus)),
            (Some(RK::CPCTPlus),  Some(RK::None),     Some(RK::CPCTPlus)),
            (None,                Some(RK::CPCTPlus), Some(RK::CPCTPlus)),
            (None,                Some(RK::None),     Some(RK::None)),
            (None,                None,               Some(RK::CPCTPlus)),
            (Some(RK::None),      None,               Some(RK::None)),
            (Some(RK::CPCTPlus),  None,               Some(RK::CPCTPlus)),
        ];

        for (i, (builder_arg, header_arg, expected_rk)) in
            recovery_kinds.iter().cloned().enumerate()
        {
            let y_src = if let Some(header_arg) = header_arg {
                format!(
                    "\
                %grmtools{{yacckind: Original(NoAction), recoverer: {}}} \
                %% \
                start: ; \
                ",
                    match header_arg {
                        RK::None => "RecoveryKind::None",
                        RK::CPCTPlus => "RecoveryKind::CPCTPlus",
                        _ => panic!("Unrecognized recoverykind"),
                    }
                )
            } else {
                r#"
                %grmtools{yacckind: Original(NoAction)}
                %%
                Start: ;
                "#
                .to_string()
            };
            let out_dir = std::env::var("OUT_DIR").unwrap();
            let y_path = format!("{out_dir}/recoverykind_test_{i}.y");
            let y_out_path = format!("{y_path}.rs");
            let l_src = r#"
%%
. ;"#;
            let l_path = format!("{out_dir}/recoverykind_tests.l");
            let l_out_path = format!("{out_dir}/recoverykind_tests_{i}.l.rs");
            std::fs::File::create(l_path.clone()).unwrap();
            std::fs::write(l_path.clone(), l_src).unwrap();
            eprintln!("{:?} {:?}", y_path, l_path);
            std::fs::File::create(y_path.clone()).unwrap();
            std::fs::write(y_path.clone(), y_src).unwrap();
            let mut cl_builder = CTLexerBuilder::new()
                .output_path(l_out_path)
                .lexer_path(l_path);
            cl_builder = cl_builder.lrpar_config(move |mut cp_builder| {
                cp_builder = cp_builder
                    .output_path(y_out_path.clone())
                    .grammar_path(y_path.clone());
                if let Some(builder_arg) = builder_arg {
                    cp_builder.recoverer(builder_arg.clone())
                } else {
                    cp_builder
                }
                .process_header(Box::new(move |_, rk, _| {
                    if match (rk, expected_rk) {
                        (RK::None, Some(RK::None)) | (RK::CPCTPlus, Some(RK::CPCTPlus)) => true,
                        _ => false,
                    } {
                        Ok(())
                    } else {
                        panic!("Unexpected recovery kind")
                    }
                }))
            });

            cl_builder.build()?;
        }
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
