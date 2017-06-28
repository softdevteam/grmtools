// Copyright (c) 2017 King's College London
// created by the Software Development Team <http://soft-dev.org/>
//
// The Universal Permissive License (UPL), Version 1.0
//
// Subject to the condition set forth below, permission is hereby granted to any person obtaining a
// copy of this software, associated documentation and/or data (collectively the "Software"), free
// of charge and under any and all copyright rights in the Software, and any and all patent rights
// owned or freely licensable by each licensor hereunder covering either (i) the unmodified
// Software as contributed to or provided by such licensor, or (ii) the Larger Works (as defined
// below), to deal in both
//
// (a) the Software, and
// (b) any piece of software and/or hardware listed in the lrgrwrks.txt file
// if one is included with the Software (each a "Larger Work" to which the Software is contributed
// by such licensors),
//
// without restriction, including without limitation the rights to copy, create derivative works
// of, display, perform, and distribute the Software and make, use, sell, offer for sale, import,
// export, have made, and have sold the Software and the Larger Work(s), and to sublicense the
// foregoing rights on either these or other terms.
//
// This license is subject to the following condition: The above copyright notice and either this
// complete permission notice or at a minimum a reference to the UPL must be included in all copies
// or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING
// BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
// NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
// DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

#![feature(try_from)]

use std::convert::TryFrom;
use std::collections::HashMap;
use std::{env, process};
use std::fs::File;
use std::io::{Read, stderr, Write};
use std::path::Path;

extern crate getopts;
use getopts::Options;

extern crate cfgrammar;
use cfgrammar::yacc::{yacc_grm, YaccKind};

extern crate lrlex;
use lrlex::{build_lex, Lexeme};

extern crate lrtable;
use lrtable::{Minimiser, yacc_to_statetable};

extern crate lrpar;
use lrpar::parser::parse;

fn usage(prog: String, msg: &str) -> ! {
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
                                .optopt("y", "yaccvariant",
                                        "Yacc variant to be parsed (default: Original)",
                                        "Original|Eco")
                                .parse(&args[1..]) {
        Ok(m) => m,
        Err(f) => usage(prog, f.to_string().as_str())
    };

    if matches.opt_present("h") {
        usage(prog, "");
    }

    let yacckind = match matches.opt_str("y") {
        None => YaccKind::Original,
        Some(s) => {
            match &*s.to_lowercase() {
                "original" => YaccKind::Original,
                "eco" => YaccKind::Eco,
                _ => usage(prog, &format!("Unknown Yacc variant '{}'.", s))
            }
        }
    };

    if matches.free.len() != 3 {
        usage(prog, "Too few arguments given.");
    }

    let lex_l_path = &matches.free[0];
    let mut lexerdef = match build_lex::<u16>(&read_file(lex_l_path)) {
        Ok(ast) => ast,
        Err(s) => {
            writeln!(&mut stderr(), "{}: {}", &lex_l_path, &s).ok();
            process::exit(1);
        }
    };

    let yacc_y_path = &matches.free[1];
    let grm = match yacc_grm(yacckind, &read_file(yacc_y_path)) {
        Ok(x) => x,
        Err(s) => {
            writeln!(&mut stderr(), "{}: {}", &yacc_y_path, &s).ok();
            process::exit(1);
        }
    };
    let stable = match yacc_to_statetable(&grm, Minimiser::Pager) {
        Ok(x) => x,
        Err(s) => {
            writeln!(&mut stderr(), "{}: {}", &yacc_y_path, &s).ok();
            process::exit(1);
        }
    };
    println!("reduce/reduce: {}\nshift/reduce: {}", stable.reduce_reduce, stable.shift_reduce);

    // Sync up the IDs of terminals in the lexer and parser
    let mut rule_ids = HashMap::<&str, u16>::new();
    for term_idx in grm.iter_term_idxs() {
        rule_ids.insert(grm.term_name(term_idx).unwrap(), u16::try_from(usize::from(term_idx)).unwrap());
    }
    lexerdef.set_rule_ids(&rule_ids);

    let input = read_file(&matches.free[2]);

    let mut lexemes = lexerdef.lexer(&input).lexemes().unwrap();
    lexemes.push(Lexeme::new(u16::try_from(usize::from(grm.end_term_idx())).unwrap(), input.len(), 0));
    let pt = parse::<u16>(&grm, &stable, &lexemes).unwrap();
    println!("{}", pt.pp(&grm, &input));
}
