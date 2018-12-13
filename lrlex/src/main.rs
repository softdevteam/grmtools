// Copyright (c) 2017 King's College London
// created by the Software Development Team <http://soft-dev.org/>
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0>, or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, or the UPL-1.0 license <http://opensource.org/licenses/UPL>
// at your option. This file may not be copied, modified, or distributed except according to those
// terms.

extern crate getopts;
extern crate lrlex;
extern crate lrpar;

use getopts::Options;
use std::{
    env,
    fs::File,
    io::{stderr, Read, Write},
    path::Path,
    process
};

use lrlex::{build_lex, LexerDef};
use lrpar::Lexer;

fn usage(prog: &str, msg: &str) {
    let path = Path::new(prog);
    let leaf = match path.file_name() {
        Some(m) => m.to_str().unwrap(),
        None => "lrpar"
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
    let lexerdef: LexerDef<usize> = build_lex(&read_file(lex_l_path)).unwrap_or_else(|s| {
        writeln!(&mut stderr(), "{}: {}", &lex_l_path, &s).ok();
        process::exit(1);
    });
    let input = &read_file(&matches.free[1]);
    let lexemes = lexerdef.lexer(input).all_lexemes().unwrap();
    for l in &lexemes {
        println!(
            "{} {}",
            lexerdef.get_rule_by_id(l.tok_id()).name.as_ref().unwrap(),
            &input[l.start()..l.end().unwrap_or(l.start())]
        );
    }
}
