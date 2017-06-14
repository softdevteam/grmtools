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

extern crate getopts;
extern crate lrlex;

use getopts::Options;
use std::{env, process};
use std::fs::File;
use std::io::{Read, stderr, Write};
use std::path::Path;

use lrlex::{build_lex, LexerDef};

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
        Err(f) => {
            usage(prog, f.to_string().as_str());
            return;
        }
    };
    if matches.opt_present("h") || matches.free.len() != 2 {
        usage(prog, "");
        return;
    }

    let lex_l_path = &matches.free[0];
    let lexerdef: LexerDef<usize> = build_lex(&read_file(lex_l_path)).unwrap_or_else(|s| {
            writeln!(&mut stderr(), "{}: {}", &lex_l_path, &s).ok();
            process::exit(1);
        });
    let input = &read_file(&matches.free[1]);
    let lexemes = lexerdef.lexer(&input).lexemes().unwrap();
    for l in lexemes.iter() {
        println!("{} {}", lexerdef.get_rule_by_id(l.tok_id()).unwrap().name.as_ref().unwrap(), &input[l.start()..l.start() + l.len()]);
    }
}
