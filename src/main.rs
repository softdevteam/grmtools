extern crate getopts;
extern crate lrlex;

use getopts::Options;
use std::{env, process};
use std::fs::File;
use std::io::{Read, stderr, Write};
use std::path::Path;

use lrlex::{build_lex, do_lex};

fn usage(prog: String, msg: &str) {
    let path = Path::new(prog.as_str());
    let leaf = match path.file_name() {
        Some(m) => m.to_str().unwrap(),
        None => "lrpar"
    };
    if msg.len() > 0 {
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
    let matches = match Options::new()
                                .optflag("h", "help", "")
                                .parse(&args[1..]) {
        Ok(m) => m,
        Err(f) => { usage(prog, f.to_string().as_str()); return }
    };

    if matches.opt_present("h") || matches.free.len() != 2 {
        usage(prog, "");
        return;
    }

    let lex_l_path = &matches.free[0];
    let lex_ast = match build_lex(&read_file(lex_l_path)) {
        Ok(ast) => ast,
        Err(s) => {
            writeln!(&mut stderr(), "{}: {}", &lex_l_path, &s).ok();
            process::exit(1);
        }
    };
    let input = &read_file(&matches.free[1]);
    let lexemes = do_lex(&lex_ast, &input).unwrap();
    for l in lexemes.iter() {
        println!("{} {}", lex_ast.get_rule_by_id(l.tok_id).unwrap().name.as_ref().unwrap(), &input[l.start..l.start + l.len]);
    }
}
