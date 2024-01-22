mod diagnostics;
use crate::diagnostics::*;
use cfgrammar::yacc::{ast::ASTWithValidityInfo, YaccGrammar, YaccKind, YaccOriginalActionKind};
use getopts::Options;
use lrlex::{DefaultLexerTypes, LRNonStreamingLexerDef, LexerDef};
use lrpar::parser::{RTParserBuilder, RecoveryKind};
use lrtable::{from_yacc, Minimiser};
use num_traits::ToPrimitive;
use std::{
    env,
    fs::File,
    io::Read,
    path::{Path, PathBuf},
    process,
};

const WARNING: &str = "[Warning]";
const ERROR: &str = "[Error]";

fn usage(prog: &str, msg: &str) -> ! {
    let path = Path::new(prog);
    let leaf = match path.file_name() {
        Some(m) => m.to_str().unwrap(),
        None => "lrpar",
    };
    if !msg.is_empty() {
        eprintln!("{}", msg);
    }
    eprintln!("Usage: {} [-r <cpctplus|none>] [-y <eco|grmtools|original>] [-q] <lexer.l> <parser.y> <input file>", leaf);
    process::exit(1);
}

fn read_file<P: AsRef<Path>>(path: P) -> String {
    let mut f = match File::open(&path) {
        Ok(r) => r,
        Err(e) => {
            eprintln!("Can't open file {}: {}", path.as_ref().display(), e);
            process::exit(1);
        }
    };
    let mut s = String::new();
    f.read_to_string(&mut s).unwrap();
    s
}

fn indent(s: &str, indent: &str) -> String {
    format!("{indent}{}\n", s.trim_end_matches('\n')).replace('\n', &format!("\n{}", indent))
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let prog = &args[0];
    let matches = match Options::new()
        .optflag("h", "help", "")
        .optflag("q", "quiet", "Don't print warnings such as conflicts")
        .optopt(
            "r",
            "recoverer",
            "Recoverer to be used (default: cpctplus)",
            "cpctplus|none",
        )
        .optopt(
            "y",
            "yaccvariant",
            "Yacc variant to be parsed (default: original)",
            "eco|original|grmtools",
        )
        .parse(&args[1..])
    {
        Ok(m) => m,
        Err(f) => usage(prog, f.to_string().as_str()),
    };

    if matches.opt_present("h") {
        usage(prog, "");
    }

    let quiet = matches.opt_present("q");

    let recoverykind = match matches.opt_str("r") {
        None => RecoveryKind::CPCTPlus,
        Some(s) => match &*s.to_lowercase() {
            "cpctplus" => RecoveryKind::CPCTPlus,
            "none" => RecoveryKind::None,
            _ => usage(prog, &format!("Unknown recoverer '{}'.", s)),
        },
    };

    let yacckind = match matches.opt_str("y") {
        None => YaccKind::Original(YaccOriginalActionKind::GenericParseTree),
        Some(s) => match &*s.to_lowercase() {
            "eco" => YaccKind::Eco,
            "grmtools" => YaccKind::Grmtools,
            "original" => YaccKind::Original(YaccOriginalActionKind::GenericParseTree),
            _ => usage(prog, &format!("Unknown Yacc variant '{}'.", s)),
        },
    };

    if matches.free.len() != 3 {
        usage(prog, "Too few arguments given.");
    }

    let lex_l_path = PathBuf::from(&matches.free[0]);
    let lex_src = read_file(&lex_l_path);
    let mut lexerdef = match LRNonStreamingLexerDef::<DefaultLexerTypes<u32>>::from_str(&lex_src) {
        Ok(ast) => ast,
        Err(errs) => {
            let formatter = SpannedDiagnosticFormatter::new(&lex_src, &lex_l_path).unwrap();
            eprintln!("{ERROR}{}", formatter.file_location_msg("", None));
            for e in errs {
                eprintln!("{}", indent(&formatter.format_error(e).to_string(), "    "));
            }
            process::exit(1);
        }
    };

    let yacc_y_path = PathBuf::from(&matches.free[1]);
    let yacc_src = read_file(&yacc_y_path);
    let ast_validation = ASTWithValidityInfo::new(yacckind, &yacc_src);
    let warnings = ast_validation.ast().warnings();
    let res = YaccGrammar::new_from_ast_with_validity_info(yacckind, &ast_validation);
    let mut yacc_diagnostic_formatter: Option<SpannedDiagnosticFormatter> = None;
    let grm = match res {
        Ok(x) => {
            if !warnings.is_empty() {
                let formatter = SpannedDiagnosticFormatter::new(&yacc_src, &yacc_y_path).unwrap();
                eprintln!("{WARNING}{}", formatter.file_location_msg("", None));
                for w in warnings {
                    eprintln!("{}", indent(&formatter.format_warning(w), "    "));
                }
                yacc_diagnostic_formatter = Some(formatter);
            }
            x
        }
        Err(errs) => {
            let formatter = SpannedDiagnosticFormatter::new(&yacc_src, &yacc_y_path).unwrap();
            eprintln!("{ERROR}{}", formatter.file_location_msg("", None));
            for e in errs {
                eprintln!("{}", indent(&formatter.format_error(e).to_string(), "    "));
            }
            eprintln!("{WARNING}{}", formatter.file_location_msg("", None));
            for w in warnings {
                eprintln!("{}", indent(&formatter.format_warning(w), "    "));
            }
            process::exit(1);
        }
    };
    let (sgraph, stable) = match from_yacc(&grm, Minimiser::Pager) {
        Ok(x) => x,
        Err(s) => {
            eprintln!("{}: {}", &yacc_y_path.display(), &s);
            process::exit(1);
        }
    };

    if !quiet {
        if let Some(c) = stable.conflicts() {
            let formatter = if let Some(yacc_diagnostic_formatter) = &yacc_diagnostic_formatter {
                yacc_diagnostic_formatter
            } else {
                let formatter = SpannedDiagnosticFormatter::new(&yacc_src, &yacc_y_path).unwrap();
                yacc_diagnostic_formatter = Some(formatter);
                yacc_diagnostic_formatter.as_ref().unwrap()
            };

            let pp_rr = if let Some(i) = grm.expectrr() {
                i != c.rr_len()
            } else {
                0 != c.rr_len()
            };
            let pp_sr = if let Some(i) = grm.expect() {
                i != c.sr_len()
            } else {
                0 != c.sr_len()
            };
            if pp_rr {
                println!("{}", c.pp_rr(&grm));
            }
            if pp_sr {
                println!("{}", c.pp_sr(&grm));
            }
            if pp_rr || pp_sr {
                println!("Stategraph:\n{}\n", sgraph.pp_core_states(&grm));
            }
            formatter.handle_conflicts::<DefaultLexerTypes<u32>>(
                &grm,
                ast_validation.ast(),
                c,
                &sgraph,
                &stable,
            );
        }
    }

    {
        let rule_ids = grm
            .tokens_map()
            .iter()
            .map(|(&n, &i)| (n, usize::from(i).to_u32().unwrap()))
            .collect();
        let (missing_from_lexer, missing_from_parser) = lexerdef.set_rule_ids(&rule_ids);
        if !quiet {
            if let Some(tokens) = missing_from_parser {
                eprintln!("Warning: these tokens are defined in the lexer but not referenced in the\ngrammar:");
                let mut sorted = tokens.iter().cloned().collect::<Vec<&str>>();
                sorted.sort_unstable();
                for n in sorted {
                    eprintln!("  {}", n);
                }
            }
            if let Some(tokens) = missing_from_lexer {
                eprintln!(
                    "Error: these tokens are referenced in the grammar but not defined in the lexer:"
                );
                let mut sorted = tokens.iter().cloned().collect::<Vec<&str>>();
                sorted.sort_unstable();
                for n in sorted {
                    eprintln!("  {}", n);
                }
                process::exit(1);
            }
        }
    }

    let input = read_file(&matches.free[2]);
    let lexer = lexerdef.lexer(&input);
    let pb = RTParserBuilder::new(&grm, &stable).recoverer(recoverykind);
    let (pt, errs) = pb.parse_generictree(&lexer);
    match pt {
        Some(pt) => println!("{}", pt.pp(&grm, &input)),
        None => println!("Unable to repair input sufficiently to produce parse tree.\n"),
    }
    for e in &errs {
        println!("{}", e.pp(&lexer, &|t| grm.token_epp(t)));
    }
    if !errs.is_empty() {
        process::exit(1);
    }
}
