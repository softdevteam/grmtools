use cfgrammar::yacc::{YaccKind, YaccOriginalActionKind};
use lrlex::{CTLexerBuilder, DefaultLexerTypes};
use lrpar::{CTParserBuilder, RecoveryKind};
use std::{
    env, fs,
    path::{Path, PathBuf},
};
use yaml_rust2::YamlLoader;

#[allow(dead_code)]
pub(crate) fn run_test_path<P: AsRef<Path>>(path: P) -> Result<(), Box<dyn std::error::Error>> {
    let out_dir = env::var("OUT_DIR").unwrap();
    let path = path.as_ref();
    if path.is_file() {
        println!("cargo::rerun-if-changed={}", path.display());
        // Parse test file
        let s = fs::read_to_string(path).unwrap();
        let docs = YamlLoader::load_from_str(&s).unwrap();
        let grm = &docs[0]["grammar"].as_str().unwrap();
        let lex = &docs[0]["lexer"].as_str().unwrap();
        let yacckind = match docs[0]["yacckind"].as_str() {
            Some("Original(YaccOriginalActionKind::NoAction)") => {
                Some(YaccKind::Original(YaccOriginalActionKind::NoAction))
            }
            Some("Original(YaccOriginalActionKind::UserAction)") => {
                Some(YaccKind::Original(YaccOriginalActionKind::UserAction))
            }
            Some("Grmtools") => Some(YaccKind::Grmtools),
            Some("Original(YaccOriginalActionKind::GenericParseTree)") => {
                Some(YaccKind::Original(YaccOriginalActionKind::GenericParseTree))
            }
            Some(s) => panic!("YaccKind '{}' not supported", s),
            None => None,
        };
        let recoverer = match docs[0]["revoverer"].as_str() {
            Some("RecoveryKind::CPCTPlus") => Some(RecoveryKind::CPCTPlus),
            Some("RecoveryKind::None") => Some(RecoveryKind::None),
            _ => None,
        };
        let (negative_yacc_flags, positive_yacc_flags) = &docs[0]["yacc_flags"]
            .as_vec()
            .map(|flags_vec| {
                flags_vec
                    .iter()
                    .partition(|flag| flag.as_str().unwrap().starts_with('!'))
            })
            .unwrap_or_else(|| (Vec::new(), Vec::new()));
        let positive_yacc_flags = positive_yacc_flags
            .iter()
            .map(|flag| flag.as_str().unwrap())
            .collect::<Vec<_>>();
        let negative_yacc_flags = negative_yacc_flags
            .iter()
            .map(|flag| {
                let flag = flag.as_str().unwrap();
                flag.strip_prefix('!').unwrap()
            })
            .collect::<Vec<_>>();
        let yacc_flags = (&positive_yacc_flags, &negative_yacc_flags);
        let (negative_lex_flags, positive_lex_flags) = &docs[0]["lex_flags"]
            .as_vec()
            .map(|flags_vec| {
                flags_vec
                    .iter()
                    .partition(|flag| flag.as_str().unwrap().starts_with('!'))
            })
            .unwrap_or_else(|| (Vec::new(), Vec::new()));
        let negative_lex_flags = negative_lex_flags
            .iter()
            .map(|flag| {
                let flag = flag.as_str().unwrap();
                flag.strip_prefix('!').unwrap()
            })
            .collect::<Vec<_>>();
        let positive_lex_flags = positive_lex_flags
            .iter()
            .map(|flag| flag.as_str().unwrap())
            .collect::<Vec<_>>();
        let lex_flags = (&positive_lex_flags, &negative_lex_flags);

        // The code below, in essence, replicates lrlex and lrpar's internal / undocumented
        // filename conventions. If those change, this code will also have to change.

        // Create grammar files
        let base = path.file_stem().unwrap().to_str().unwrap();
        let mut pg = PathBuf::from(&out_dir);
        pg.push(format!("{}.test.y", base));
        fs::write(&pg, grm).unwrap();
        let mut pl = PathBuf::from(&out_dir);
        pl.push(format!("{}.test.l", base));
        fs::write(&pl, lex).unwrap();

        // Build parser and lexer
        let mut outp = PathBuf::from(&out_dir);
        outp.push(format!("{}.y.rs", base));
        outp.set_extension("rs");
        let mut cp_build = CTParserBuilder::<DefaultLexerTypes<u32>>::new();
        if let Some(yacckind) = yacckind {
            cp_build = cp_build.yacckind(yacckind);
        }
        if let Some(recoverer) = recoverer {
            cp_build = cp_build.recoverer(recoverer)
        }
        cp_build = cp_build
            .grammar_path(pg.to_str().unwrap())
            .output_path(&outp);
        if let Some(flag) = check_flag(yacc_flags, "error_on_conflicts") {
            cp_build = cp_build.error_on_conflicts(flag)
        }
        if let Some(flag) = check_flag(yacc_flags, "warnings_are_errors") {
            cp_build = cp_build.warnings_are_errors(flag)
        }
        if let Some(flag) = check_flag(yacc_flags, "show_warnings") {
            cp_build = cp_build.show_warnings(flag)
        };
        let cp = cp_build.build()?;

        let mut outl = PathBuf::from(&out_dir);
        outl.push(format!("{}.l.rs", base));
        outl.set_extension("rs");
        let mut cl_build = CTLexerBuilder::new()
            .rule_ids_map(cp.token_map())
            .lexer_path(pl.to_str().unwrap())
            .output_path(&outl);
        if let Some(flag) = check_flag(lex_flags, "allow_missing_terms_in_lexer") {
            cl_build = cl_build.allow_missing_terms_in_lexer(flag)
        }
        if let Some(flag) = check_flag(lex_flags, "allow_missing_tokens_in_parser") {
            cl_build = cl_build.allow_missing_tokens_in_parser(flag)
        }
        if let Some(flag) = check_flag(lex_flags, "dot_matches_new_line") {
            cl_build = cl_build.dot_matches_new_line(flag)
        }
        if let Some(flag) = check_flag(lex_flags, "case_insensitive") {
            cl_build = cl_build.case_insensitive(flag)
        }
        if let Some(flag) = check_flag(lex_flags, "multi_line") {
            cl_build = cl_build.multi_line(flag)
        }
        if let Some(flag) = check_flag(lex_flags, "swap_greed") {
            cl_build = cl_build.swap_greed(flag)
        }
        if let Some(flag) = check_flag(lex_flags, "ignore_whitespace") {
            cl_build = cl_build.ignore_whitespace(flag)
        }
        if let Some(flag) = check_flag(lex_flags, "unicode") {
            cl_build = cl_build.unicode(flag)
        }
        if let Some(flag) = check_flag(lex_flags, "octal") {
            cl_build = cl_build.octal(flag)
        }
        cl_build.build()?;
    }
    Ok(())
}

fn check_flag((positive, negative): (&Vec<&str>, &Vec<&str>), flag: &str) -> Option<bool> {
    assert_eq!(
        positive.contains(&flag) | negative.contains(&flag),
        positive.contains(&flag) ^ negative.contains(&flag)
    );
    if positive.contains(&flag) {
        Some(true)
    } else if negative.contains(&flag) {
        Some(false)
    } else {
        None
    }
}
