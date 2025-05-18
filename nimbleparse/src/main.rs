use cfgrammar::{
    header::{GrmtoolsSectionParser, Header, HeaderError, HeaderValue, Value},
    markmap::Entry,
    yacc::{ast::ASTWithValidityInfo, YaccGrammar, YaccKind, YaccOriginalActionKind},
    Location, Span,
};
use getopts::Options;
use lrlex::{DefaultLexerTypes, LRLexError, LRNonStreamingLexerDef, LexerDef};
use lrpar::{
    diagnostics::{DiagnosticFormatter, SpannedDiagnosticFormatter},
    parser::{RTParserBuilder, RecoveryKind},
    LexerTypes,
};
use lrtable::{from_yacc, Minimiser, StateTable};
use num_traits::AsPrimitive;
use num_traits::ToPrimitive as _;
use std::{
    env,
    error::Error,
    fmt,
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
    eprintln!("Usage: {} [-r <cpctplus|none>] [-y <eco|grmtools|original>] [-dq] <lexer.l> <parser.y> <input files> ...", leaf);
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

/// Indents a multi-line string and trims any trailing newline.
/// This currently assumes that indentation on blank lines does not matter.
///
/// The algorithm used by this function is:
/// 1. Prefix `s` with the indentation, indenting the first line.
/// 2. Trim any trailing newlines.
/// 3. Replace all newlines with `\n{indent}`` to indent all lines after the first.
///
/// It is plausible that we should a step 4, but currently do not:
/// 4. Replace all `\n{indent}\n` with `\n\n`
fn indent(s: &str, indent: &str) -> String {
    format!("{indent}{}\n", s.trim_end_matches('\n')).replace('\n', &format!("\n{}", indent))
}

pub fn set_rule_ids<LexerTypesT: LexerTypes<StorageT = u32>, LT: LexerDef<LexerTypesT>>(
    lexerdef: &mut LT,
    grm: &YaccGrammar,
) -> (Option<Vec<Span>>, Option<Vec<Span>>)
where
    usize: num_traits::AsPrimitive<LexerTypesT::StorageT>,
{
    let rule_ids = grm
        .tokens_map()
        .iter()
        .map(|(&n, &i)| (n, usize::from(i).to_u32().unwrap()))
        .collect::<std::collections::HashMap<&str, u32>>();
    let (missing_from_lexer, missing_from_parser) = lexerdef.set_rule_ids_spanned(&rule_ids);
    let missing_from_lexer = missing_from_lexer.map(|tokens| {
        tokens
            .iter()
            .map(|name| {
                grm.token_span(*grm.tokens_map().get(name).unwrap())
                    .expect("Given token should have a span")
            })
            .collect::<Vec<_>>()
    });

    let missing_from_parser =
        missing_from_parser.map(|tokens| tokens.iter().map(|(_, span)| *span).collect::<Vec<_>>());
    (missing_from_lexer, missing_from_parser)
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let prog = &args[0];
    let matches = match Options::new()
        .optflag("h", "help", "")
        .optflag("q", "quiet", "Don't print warnings such as conflicts")
        .optflag("d", "dump-state-graph", "Print the parser state graph")
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

    let dump_state_graph = matches.opt_present("d");
    let quiet = matches.opt_present("q");
    let mut header = Header::new();
    match matches.opt_str("r") {
        None => (),
        Some(s) => {
            header.set_merge_behavior(
                &"recoverer".to_string(),
                cfgrammar::markmap::MergeBehavior::Ours,
            );
            header.insert(
                "recoverer".to_string(),
                HeaderValue(
                    Location::CommandLine,
                    Value::try_from(match &*s.to_lowercase() {
                        "cpctplus" => RecoveryKind::CPCTPlus,
                        "none" => RecoveryKind::None,
                        _ => usage(prog, &format!("Unknown recoverer '{}'.", s)),
                    })
                    .expect("All these RecoveryKinds should convert without error"),
                ),
            );
        }
    };
    let entry = match header.entry("yacckind".to_string()) {
        Entry::Occupied(_) => unreachable!("Header should be empty"),
        Entry::Vacant(v) => v,
    };
    match matches.opt_str("y") {
        None => {}
        Some(s) => {
            entry.insert_entry(HeaderValue(
                Location::CommandLine,
                Value::try_from(match &*s.to_lowercase() {
                    "eco" => YaccKind::Eco,
                    "grmtools" => YaccKind::Grmtools,
                    "original" => YaccKind::Original(YaccOriginalActionKind::GenericParseTree),
                    _ => usage(prog, &format!("Unknown Yacc variant '{}'.", s)),
                })
                .expect("All these yacckinds should convert without error"),
            ));
        }
    };
    let args_len = matches.free.len();
    if args_len < 2 {
        usage(prog, "Too few arguments given.");
    }

    let lex_l_path = PathBuf::from(&matches.free[0]);
    let lex_src = read_file(&lex_l_path);
    let lex_diag = SpannedDiagnosticFormatter::new(&lex_src, &lex_l_path);
    let mut lexerdef = match LRNonStreamingLexerDef::<DefaultLexerTypes<u32>>::from_str(&lex_src) {
        Ok(ast) => ast,
        Err(errs) => {
            eprintln!("{ERROR}{}", lex_diag.file_location_msg("", None));
            for e in errs {
                eprintln!("{}", indent(&lex_diag.format_error(e).to_string(), "    "));
            }
            process::exit(1);
        }
    };

    let yacc_y_path = PathBuf::from(&matches.free[1]);
    let yacc_src = read_file(&yacc_y_path);
    let yacc_diag = SpannedDiagnosticFormatter::new(&yacc_src, &yacc_y_path);
    let yk_val = header.get("yacckind");
    if yk_val.is_none() {
        let parsed_header = GrmtoolsSectionParser::new(&yacc_src, true).parse();
        match parsed_header {
            Ok((parsed_header, _)) => {
                header
                    .merge_from(parsed_header)
                    .expect("Specified merge behavior cannot fail");
            }
            Err(errs) => {
                eprintln!(
                    "{ERROR}{}",
                    yacc_diag.file_location_msg(" parsing the `%grmtools` section:", None)
                );
                for e in errs {
                    eprintln!("{}", indent(&yacc_diag.format_error(e).to_string(), "    "));
                }
                std::process::exit(1);
            }
        }
    }
    let yk_val = header.get("yacckind");
    if yk_val.is_none() {
        eprintln!("yacckind not specified in the %grmtools section of the grammar or via the '-y' parameter");
        std::process::exit(1);
    }
    let HeaderValue(_, yk_val) = yk_val.unwrap();
    let yacc_kind = YaccKind::try_from(yk_val).unwrap_or(YaccKind::Grmtools);
    let ast_validation = ASTWithValidityInfo::new(yacc_kind, &yacc_src);
    let recoverykind = if let Some(HeaderValue(_, rk_val)) = header.get("recoverer") {
        match RecoveryKind::try_from(rk_val) {
            Err(e) => {
                eprintln!(
                    "{ERROR}{}",
                    yacc_diag.file_location_msg(" parsing the `%grmtools` section:", None)
                );
                let spanned_e: HeaderError<Span> = HeaderError {
                    kind: e.kind,
                    locations: e
                        .locations
                        .iter()
                        .map(|l| match l {
                            Location::Span(span) => *span,
                            _ => unreachable!("All reachable errors should contain spans"),
                        })
                        .collect::<Vec<_>>(),
                };
                eprintln!(
                    "{}",
                    indent(&yacc_diag.format_error(spanned_e).to_string(), "    ")
                );
                process::exit(1)
            }
            Ok(rk) => rk,
        }
    } else {
        // Fallback to the default recoverykind
        RecoveryKind::CPCTPlus
    };
    let warnings = ast_validation.ast().warnings();
    let res = YaccGrammar::new_from_ast_with_validity_info(&ast_validation);
    let grm = match res {
        Ok(x) => {
            if !warnings.is_empty() {
                eprintln!("{WARNING}{}", yacc_diag.file_location_msg("", None));
                for w in warnings {
                    eprintln!("{}", indent(&yacc_diag.format_warning(w), "    "));
                }
            }
            x
        }
        Err(errs) => {
            eprintln!("{ERROR}{}", yacc_diag.file_location_msg("", None));
            for e in errs {
                eprintln!("{}", indent(&yacc_diag.format_error(e).to_string(), "    "));
            }
            eprintln!("{WARNING}{}", yacc_diag.file_location_msg("", None));
            for w in warnings {
                eprintln!("{}", indent(&yacc_diag.format_warning(w), "    "));
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

    if dump_state_graph {
        println!("Stategraph:\n{}\n", sgraph.pp_core_states(&grm));
    }

    if !quiet {
        if let Some(c) = stable.conflicts() {
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
            if (pp_rr || pp_sr) && !dump_state_graph {
                println!("Stategraph:\n{}\n", sgraph.pp_core_states(&grm));
            }
            yacc_diag.handle_conflicts::<DefaultLexerTypes<u32>>(
                &grm,
                ast_validation.ast(),
                c,
                &sgraph,
                &stable,
            );
        }
    }

    let (missing_from_lexer, missing_from_parser) = set_rule_ids(&mut lexerdef, &grm);
    {
        if !quiet {
            if let Some(token_spans) = missing_from_lexer {
                let warn_indent = " ".repeat(WARNING.len());
                eprintln!(
                    "{WARNING} these tokens are not referenced in the lexer but defined as follows"
                );
                eprintln!(
                    "{warn_indent} {}",
                    yacc_diag.file_location_msg("in the grammar", None)
                );
                for span in token_spans {
                    eprintln!(
                        "{}",
                        yacc_diag.underline_span_with_text(
                            span,
                            "Missing from lexer".to_string(),
                            '^'
                        )
                    );
                }
                eprintln!();
            }
            if let Some(token_spans) = missing_from_parser {
                let err_indent = " ".repeat(ERROR.len());
                eprintln!(
                    "{ERROR} these tokens are not referenced in the grammar but defined as follows"
                );
                eprintln!(
                    "{err_indent} {}",
                    lex_diag.file_location_msg("in the lexer", None)
                );
                for span in token_spans {
                    eprintln!(
                        "{}",
                        lex_diag.underline_span_with_text(
                            span,
                            "Missing from parser".to_string(),
                            '^'
                        )
                    );
                }
                process::exit(1);
            }
        }
    }

    let parser_build_ctxt = ParserBuildCtxt {
        header,
        lexerdef,
        grm,
        stable,
        yacc_y_path,
        recoverykind,
    };

    if matches.free.len() == 3 {
        let input_path = PathBuf::from(&matches.free[2]);
        // If there is only one input file we want to print the generic parse tree.
        // We also want to handle `-` as stdin.
        let input = if &matches.free[2] == "-" {
            let mut s = String::new();
            std::io::stdin().read_to_string(&mut s).unwrap();
            s
        } else {
            read_file(&matches.free[2])
        };
        if let Err(e) = parser_build_ctxt.parse_string(input_path, input) {
            eprintln!("{}", e);
            process::exit(1);
        }
    } else if let Err(e) = parser_build_ctxt.parse_many(&matches.free[2..]) {
        eprintln!("{}", e);
        process::exit(1);
    }
}

struct ParserBuildCtxt<LexerTypesT>
where
    LexerTypesT: LexerTypes,
    usize: AsPrimitive<LexerTypesT::StorageT>,
{
    header: Header<Location>,
    lexerdef: LRNonStreamingLexerDef<LexerTypesT>,
    grm: YaccGrammar<LexerTypesT::StorageT>,
    yacc_y_path: PathBuf,
    stable: StateTable<LexerTypesT::StorageT>,
    recoverykind: RecoveryKind,
}

#[derive(Debug)]
enum NimbleparseError {
    Source {
        // We could consider including the source text here and
        // using the span error formatting machinery.
        src_path: PathBuf,
        errs: Vec<String>,
    },
    Glob(glob::GlobError),
    Pattern(glob::PatternError),
    Other(Box<dyn Error>),
}

impl From<glob::GlobError> for NimbleparseError {
    fn from(it: glob::GlobError) -> Self {
        NimbleparseError::Glob(it)
    }
}

impl From<Box<dyn Error>> for NimbleparseError {
    fn from(it: Box<dyn Error>) -> Self {
        NimbleparseError::Other(it)
    }
}

impl From<glob::PatternError> for NimbleparseError {
    fn from(it: glob::PatternError) -> Self {
        NimbleparseError::Pattern(it)
    }
}

impl Error for NimbleparseError {}

impl fmt::Display for NimbleparseError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Source { src_path, errs } => {
                writeln!(f, "While parsing: {}", src_path.display())?;
                for e in errs {
                    writeln!(f, "{}", e)?
                }
                Ok(())
            }
            Self::Glob(e) => {
                write!(f, "{}", e)
            }
            Self::Pattern(e) => {
                write!(f, "{}", e)
            }
            Self::Other(e) => {
                write!(f, "{}", e)
            }
        }
    }
}

impl<LexerTypesT> ParserBuildCtxt<LexerTypesT>
where
    LexerTypesT: LexerTypes<LexErrorT = LRLexError>,
    usize: AsPrimitive<LexerTypesT::StorageT>,
    LexerTypesT::StorageT: TryFrom<usize>,
{
    fn parse_string(self, input_path: PathBuf, input_src: String) -> Result<(), NimbleparseError> {
        let lexer = self.lexerdef.lexer(&input_src);
        let pb = RTParserBuilder::new(&self.grm, &self.stable).recoverer(self.recoverykind);
        let (pt, errs) = pb.parse_generictree(&lexer);
        match pt {
            Some(pt) => println!("{}", pt.pp(&self.grm, &input_src)),
            None => println!("Unable to repair input sufficiently to produce parse tree.\n"),
        }
        if !errs.is_empty() {
            return Err(NimbleparseError::Source {
                src_path: input_path,
                errs: errs
                    .iter()
                    .map(|e| e.pp(&lexer, &|t| self.grm.token_epp(t)))
                    .collect::<Vec<_>>(),
            });
        }
        Ok(())
    }

    fn parse_many(self, input_paths: &[String]) -> Result<(), NimbleparseError> {
        let input_paths = if input_paths.is_empty() {
            // If given no input paths, try to find some with `test_files` in the header.
            if let Some(HeaderValue(_, val)) = self.header.get("test_files") {
                let s = val.expect_string_with_context("'test_files' in %grmtools")?;
                if let Some(yacc_y_path_dir) = self.yacc_y_path.parent() {
                    let joined = yacc_y_path_dir.join(s);
                    let joined = joined.as_os_str().to_str();
                    if let Some(s) = joined {
                        let mut paths = glob::glob(s)?.peekable();
                        if paths.peek().is_none() {
                            return Err(NimbleparseError::Other(
                                format!("'test_files' glob '{}' matched no paths", s)
                                    .to_string()
                                    .into(),
                            ));
                        }
                        let mut input_paths = Vec::new();
                        for path in paths {
                            input_paths.push(path?);
                        }
                        input_paths
                    } else {
                        return Err(NimbleparseError::Other(
                            format!(
                                "Unable to convert joined path to str {} with glob '{}'",
                                self.yacc_y_path.display(),
                                s
                            )
                            .into(),
                        ));
                    }
                } else {
                    return Err(NimbleparseError::Other(
                        format!(
                            "Unable to find parent path for {}",
                            self.yacc_y_path.display()
                        )
                        .into(),
                    ));
                }
            } else {
                return Err(NimbleparseError::Other(
                    "Missing <input file> argument".into(),
                ));
            }
        } else {
            // Just convert the given arguments to paths.
            input_paths
                .iter()
                .map(PathBuf::from)
                .collect::<Vec<PathBuf>>()
        };
        if input_paths.is_empty() {
            return Err(NimbleparseError::Other(
                "Missing <input file> argument".into(),
            ));
        }
        let pb = RTParserBuilder::new(&self.grm, &self.stable).recoverer(self.recoverykind);
        // Actually parse the given arguments or the `test_files` specified in the grammar.
        for input_path in input_paths {
            let input = read_file(&input_path);
            let lexer = self.lexerdef.lexer(&input);
            let (pt, errs) = pb.parse_generictree(&lexer);
            if errs.is_empty() && pt.is_some() {
                // Since we're parsing many files, don't output all of their parse trees, just print the file name.
                println!("parsed: {}", input_path.display())
            } else {
                if pt.is_none() {
                    eprintln!(
                        "Unable to repair input at '{}' sufficiently to produce parse tree.\n",
                        input_path.display()
                    );
                }
                return Err(NimbleparseError::Source {
                    src_path: input_path,
                    errs: errs
                        .iter()
                        .map(|e| e.pp(&lexer, &|t| self.grm.token_epp(t)))
                        .collect::<Vec<_>>(),
                });
            }
        }
        Ok(())
    }
}
