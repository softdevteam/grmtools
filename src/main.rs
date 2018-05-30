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

extern crate cfgrammar;
extern crate getopts;
extern crate lrlex;
extern crate lrtable;
extern crate lrpar;
extern crate num_traits;

use std::{env, process};
use std::fs::File;
use std::io::{Read, stderr, Write};
use std::path::Path;

use getopts::Options;
use cfgrammar::yacc::{yacc_grm, YaccKind};
use lrlex::build_lex;
use lrtable::{Minimiser, from_yacc};
use lrpar::parser::{parse_rcvry, ParseRepair, RecoveryKind};
use num_traits::ToPrimitive;

fn usage(prog: &str, msg: &str) -> ! {
    let path = Path::new(prog);
    let leaf = match path.file_name() {
        Some(m) => m.to_str().unwrap(),
        None => "lrpar"
    };
    if !msg.is_empty() {
        writeln!(&mut stderr(), "{}", msg).ok();
    }
    writeln!(&mut stderr(),
             "Usage: {} [-r <cpctplus|cpctplusdyndist|mf|none>] [-y <eco|original>] <lexer.l> <parser.y> <input file>",
             leaf).ok();
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
    let prog = &args[0];
    let matches = match Options::new()
                                .optflag("h", "help", "")
                                .optopt("r", "recoverer",
                                        "Recoverer to be used (default: mf)",
                                        "cpctplus|mf|none")
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

    let recoverykind = match matches.opt_str("r") {
        None => RecoveryKind::MF,
        Some(s) => {
            match &*s.to_lowercase() {
                "cpctplus" => RecoveryKind::CPCTPlus,
                "mf" => RecoveryKind::MF,
                "none" => RecoveryKind::None,
                _ => usage(prog, &format!("Unknown recoverer '{}'.", s))
            }
        }
    };

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
    let (sgraph, stable) = match from_yacc(&grm, Minimiser::Pager) {
        Ok(x) => x,
        Err(s) => {
            writeln!(&mut stderr(), "{}: {}", &yacc_y_path, &s).ok();
            process::exit(1);
        }
    };

    {
        let rule_ids = grm.terms_map().iter()
                                      .map(|(&n, &i)| (n, usize::from(i).to_u16().unwrap()))
                                      .collect();
        let (missing_from_lexer, missing_from_parser) = lexerdef.set_rule_ids(&rule_ids);
        if let Some(tokens) = missing_from_parser {
            writeln!(&mut stderr(), "Warning: these tokens are defined in the lexer but not referenced in the\ngrammar:").ok();
            let mut sorted = tokens.iter()
                                   .cloned()
                                   .collect::<Vec<&str>>();
            sorted.sort();
            for n in sorted {
                writeln!(&mut stderr(), "  {}", n).ok();
            }
        }
        if let Some(tokens) = missing_from_lexer {
            writeln!(&mut stderr(), "Error: these tokens are referenced in the grammar but not defined in the lexer:").ok();
            let mut sorted = tokens.iter()
                                   .cloned()
                                   .collect::<Vec<&str>>();
            sorted.sort();
            for n in sorted {
                writeln!(&mut stderr(), "  {}", n).ok();
            }
            process::exit(1);
        }
    }

    let input = read_file(&matches.free[2]);
    let lexer = lexerdef.lexer(&input);
    let lexemes = lexer.lexemes().unwrap();
    let term_cost = |_| 1; // Cost of inserting/deleting a terminal
    match parse_rcvry::<u16, _>(recoverykind, &grm, &term_cost, &sgraph, &stable, &lexemes) {
        Ok(pt) => println!("{}", pt.pp(&grm, &input)),
        Err((o_pt, errs)) => {
            match o_pt {
                Some(pt) => println!("{}", pt.pp(&grm, &input)),
                None     => println!("Unable to repair input sufficiently to produce parse tree.\n")
            }
            for e in errs {
                let (line, col) = lexer.line_and_col(e.lexeme()).unwrap();
                if e.repairs().is_empty() {
                    println!("Error at line {} col {}. No repairs found.", line, col);
                    continue;
                }
                println!("Error at line {} col {}. Repairs found:", line, col);
                for repair in e.repairs() {
                    let mut lex_idx = e.lexeme_idx();
                    let mut out = vec![];
                    for r in repair.iter() {
                        match *r {
                            ParseRepair::InsertSeq(ref seqs) => {
                                let mut s = String::new();
                                s.push_str("Insert {");
                                for (i, seq) in seqs.iter().enumerate() {
                                    if i > 0 {
                                        s.push_str(", ");
                                    }
                                    for (j, t_idx) in seq.iter().enumerate() {
                                        if j > 0 {
                                            s.push_str(" ");
                                        }
                                        s.push_str(grm.term_name(*t_idx).unwrap());
                                    }
                                }
                                s.push_str("}");
                                out.push(s);
                            },
                            ParseRepair::Insert(term_idx) =>
                                out.push(format!("Insert \"{}\"", grm.term_name(term_idx).unwrap())),
                            ParseRepair::Delete | ParseRepair::Shift => {
                                let l = lexemes[lex_idx];
                                let t = &input[l.start()..l.start() + l.len()].replace("\n", "\\n");
                                if let ParseRepair::Delete = *r {
                                    out.push(format!("Delete \"{}\"", t));
                                } else {
                                    out.push(format!("Shift \"{}\"", t));
                                }
                                lex_idx += 1;
                            }
                        }
                    }
                    println!("  {}", out.join(", "));
                }
            }
            process::exit(1);
        }
    }
}
