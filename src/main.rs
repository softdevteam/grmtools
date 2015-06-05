#![feature(exit_status)]
#![feature(convert)]

extern crate getopts;
extern crate lrpar;

use getopts::Options;
use std::env;
use std::fs::File;
use std::io::{Read, stderr, Write};
use std::path::Path;

use lrpar::parse_yacc;

fn usage(prog: String, msg: &str) {
    let path = Path::new(prog.as_str());
    let leaf = match path.file_name() {
        Some(m) => m.to_str().unwrap(),
        None => "lrpar"
    };
    writeln!(&mut stderr(), "Usage: {} <filename>", leaf).ok();
    env::set_exit_status(1);
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
            env::set_exit_status(1);
            return;
        }
    };
    let mut s = String::new();
    f.read_to_string(&mut s).unwrap();

    let ast = parse_yacc(&s);
    println!("{:?}", ast);
}
