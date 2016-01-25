#![cfg_attr(test, allow(dead_code))]
#![feature(convert)]

extern crate getopts;
extern crate lrtable;

use getopts::Options;
use std::{env, process};
use std::fs::File;
use std::io::{Read, stderr, Write};
use std::path::Path;

use lrtable::from_yacc;
use lrtable::stategraph::StateGraph;
use lrtable::statetable::StateTable;
use lrtable::grammar::ast_to_grammar;

fn usage(prog: String, msg: &str) {
    let path = Path::new(prog.as_str());
    let leaf = match path.file_name() {
        Some(m) => m.to_str().unwrap(),
        None => "lrpar"
    };
    if msg.len() > 0 {
        writeln!(&mut stderr(), "{}\nUsage: {} <filename>", msg, leaf).ok();
    } else {
        writeln!(&mut stderr(), "Usage: {} <filename>", leaf).ok();
    }
    process::exit(1);
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

    if matches.opt_present("h") || matches.free.len() != 1 {
        usage(prog, "");
        return;
    }

    let p = matches.free[0].clone();
    let mut f = match File::open(&p) {
        Ok(r) => r,
        Err(e) => {
            writeln!(&mut stderr(), "Can't open file {}: {}", &p, e).ok();
            process::exit(1);
        }
    };
    let mut s = String::new();
    f.read_to_string(&mut s).unwrap();

    match from_yacc(&s) {
        Ok(ast) => {
            let grm = ast_to_grammar(&ast);
            let sg = StateGraph::new(&grm);
            StateTable::new(&grm, &sg);
        },
        Err(s) => {
            println!("Error: {}", &s);
            process::exit(1);
        }
    }
}
