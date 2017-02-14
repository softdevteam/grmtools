#![cfg_attr(test, allow(dead_code))]

use std::collections::HashMap;
use std::{env, process};
use std::fs::File;
use std::io::{Read, stderr, Write};
use std::path::Path;

extern crate getopts;
use getopts::Options;

extern crate lrlex;
use lrlex::{build_lex, do_lex, Lexeme};

extern crate lrtable;
use lrtable::yacc_to_statetable;

extern crate lrpar;
use lrpar::parse;

fn usage(prog: String, msg: &str) {
    let path = Path::new(prog.as_str());
    let leaf = match path.file_name() {
        Some(m) => m.to_str().unwrap(),
        None => "lrpar"
    };
    if msg.len() > 0 {
        writeln!(&mut stderr(), "{}", msg).ok();
    }
    writeln!(&mut stderr(), "Usage: {} <lexer.l> <parser.y> <input file>", leaf).ok();
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

    if matches.opt_present("h") || matches.free.len() != 3 {
        usage(prog, "");
        return;
    }

    let lex_l_path = &matches.free[0];
    let mut lexer = match build_lex(&read_file(lex_l_path)) {
        Ok(ast) => ast,
        Err(s) => {
            writeln!(&mut stderr(), "{}: {}", &lex_l_path, &s).ok();
            process::exit(1);
        }
    };

    let yacc_y_path = &matches.free[1];
    let (grm, stable) = match yacc_to_statetable(&read_file(yacc_y_path)) {
        Ok(x) => x,
        Err(s) => {
            writeln!(&mut stderr(), "{}: {}", &yacc_y_path, &s).ok();
            process::exit(1);
        }
    };

    // Sync up the IDs of terminals in the lexer and parser
    let mut rule_ids = HashMap::<&str, usize>::new();
    for (i, n) in grm.terminal_names.iter().enumerate() {
        rule_ids.insert(&*n, i);
    }
    lexer.set_rule_ids(&rule_ids);

    let input = read_file(&matches.free[2]);

    let mut lexemes = do_lex(&lexer, &input).unwrap();
    lexemes.push(Lexeme{tok_id: grm.end_term, start: input.len(), len: 0});
    let pt = parse(&grm, &stable, &lexemes).unwrap();
    println!("{}", pt.pp(&grm, &input));
}
