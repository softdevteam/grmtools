use getopts::Options;
use std::{
    env,
    error::Error,
    fmt,
    fs::File,
    io::{Read, Write, stderr, stdin},
    path::Path,
    process,
};

use cfgrammar::header::{GrmtoolsSectionParser, HeaderValue};
use lrlex::{DefaultLexerTypes, LRNonStreamingLexerDef, LexFlags, LexerDef, LexerKind};
use lrpar::{
    Lexeme, Lexer,
    diagnostics::{DiagnosticFormatter, SpannedDiagnosticFormatter},
};

const ERROR: &str = "[Error]";

/// A string which uses `Display` for it's `Debug` impl.
struct ErrorString(String);
impl fmt::Display for ErrorString {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let ErrorString(s) = self;
        write!(f, "{}", s)
    }
}
impl fmt::Debug for ErrorString {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let ErrorString(s) = self;
        write!(f, "{}", s)
    }
}
impl Error for ErrorString {}

fn usage(prog: &str, msg: &str) {
    let path = Path::new(prog);
    let leaf = match path.file_name() {
        Some(m) => m.to_str().unwrap(),
        None => "lrpar",
    };
    if !msg.is_empty() {
        writeln!(stderr(), "{}", msg).ok();
    }
    writeln!(stderr(), "Usage: {} <lexer.l> <input file>", leaf).ok();
    process::exit(1);
}

fn read_file(path: &str) -> String {
    let mut s = String::new();
    if path == "-" {
        stdin().read_to_string(&mut s).unwrap();
        return s;
    }
    let mut f = match File::open(path) {
        Ok(r) => r,
        Err(e) => {
            writeln!(stderr(), "Can't open file {}: {}", path, e).ok();
            process::exit(1);
        }
    };
    f.read_to_string(&mut s).unwrap();
    s
}

fn main() -> Result<(), Box<dyn Error>> {
    let args: Vec<String> = env::args().collect();
    let prog = args[0].clone();
    let matches = match Options::new().optflag("h", "help", "").parse(&args[1..]) {
        Ok(m) => m,
        Err(f) => {
            usage(&prog, f.to_string().as_str());
            return Ok(());
        }
    };
    if matches.opt_present("h") || matches.free.len() != 2 {
        usage(&prog, "");
        return Ok(());
    }

    let lex_l_path = &matches.free[0];
    let lex_src = read_file(lex_l_path);
    let lex_diag = SpannedDiagnosticFormatter::new(&lex_src, Path::new(lex_l_path));
    let (mut header, _) = match GrmtoolsSectionParser::new(&lex_src, false).parse() {
        Ok(x) => x,
        Err(es) => {
            eprintln!(
                "\n{ERROR}{}",
                lex_diag.file_location_msg(" parsing the `%grmtools` section", None)
            );
            for e in es {
                eprintln!(
                    "{}",
                    &indent("     ", &lex_diag.format_error(e).to_string())
                );
            }
            process::exit(1);
        }
    };
    header.mark_used(&"lexerkind".to_string());
    let lexerkind = if let Some(HeaderValue(_, lk_val)) = header.get("lexerkind") {
        LexerKind::try_from(lk_val)?
    } else {
        LexerKind::LRNonStreamingLexer
    };

    let lexerdef = match lexerkind {
        LexerKind::LRNonStreamingLexer => {
            let lex_flags = LexFlags::try_from(&mut header)?;
            match LRNonStreamingLexerDef::<DefaultLexerTypes<u32>>::new_with_options(
                &lex_src, lex_flags,
            ) {
                Ok(x) => x,
                Err(errs) => {
                    eprintln!("\n{ERROR}{}", lex_diag.file_location_msg("", None));
                    for e in errs {
                        eprintln!(
                            "{}",
                            &indent("     ", &lex_diag.format_error(e).to_string())
                        );
                    }
                    process::exit(1);
                }
            }
        }
        _ => {
            return Err(ErrorString("Unrecognized lexer kind".to_string()))?;
        }
    };
    {
        let unused_header_values = header.unused();
        if !unused_header_values.is_empty() {
            Err(ErrorString(format!(
                "Unused header values: {}",
                unused_header_values.join(", ")
            )))?
        }
    }
    let input = &read_file(&matches.free[1]);
    for r in lexerdef.lexer(input).iter() {
        match r {
            Ok(l) => println!(
                "{} {}",
                lexerdef.get_rule_by_id(l.tok_id()).name().unwrap(),
                &input[l.span().start()..l.span().end()]
            ),
            Err(e) => {
                println!("{:?}", e);
                process::exit(1);
            }
        }
    }
    Ok(())
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
fn indent(indent: &str, s: &str) -> String {
    format!("{indent}{}\n", s.trim_end_matches('\n')).replace('\n', &format!("\n{}", indent))
}
