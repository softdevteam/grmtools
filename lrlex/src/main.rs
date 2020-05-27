use getopts::Options;
use std::{
    env,
    fs::File,
    io::{stderr, Read, Write},
    path::Path,
    process,
};

use lrlex::{LRNonStreamingLexerDef, LexerDef};
use lrpar::Lexer;

fn usage(prog: &str, msg: &str) {
    let path = Path::new(prog);
    let leaf = match path.file_name() {
        Some(m) => m.to_str().unwrap(),
        None => "lrpar",
    };
    if !msg.is_empty() {
        writeln!(&mut stderr(), "{}", msg).ok();
    }
    writeln!(&mut stderr(), "Usage: {} <lexer.l> <input file>", leaf).ok();
    process::exit(1);
}

fn read_file(path: &str) -> String {
    let mut f = match File::open(path) {
        Ok(r) => r,
        Err(e) => {
            writeln!(&mut stderr(), "Can't open file {}: {}", path, e).ok();
            process::exit(1);
        }
    };
    let mut s = String::new();
    f.read_to_string(&mut s).unwrap();
    s
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let prog = args[0].clone();
    let matches = match Options::new().optflag("h", "help", "").parse(&args[1..]) {
        Ok(m) => m,
        Err(f) => {
            usage(&prog, f.to_string().as_str());
            return;
        }
    };
    if matches.opt_present("h") || matches.free.len() != 2 {
        usage(&prog, "");
        return;
    }

    let lex_l_path = &matches.free[0];
    let lexerdef = LRNonStreamingLexerDef::<usize>::from_str(&read_file(lex_l_path))
        .unwrap_or_else(|s| {
            writeln!(&mut stderr(), "{}: {}", &lex_l_path, &s).ok();
            process::exit(1);
        });
    let input = &read_file(&matches.free[1]);
    for r in lexerdef.lexer(input).iter() {
        match r {
            Ok(l) => println!(
                "{} {}",
                lexerdef.get_rule_by_id(l.tok_id()).name.as_ref().unwrap(),
                &input[l.span().start()..l.span().end()]
            ),
            Err(e) => {
                println!("{:?}", e);
                process::exit(1);
            }
        }
    }
}
