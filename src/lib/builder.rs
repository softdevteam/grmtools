// Copyright (c) 2018 King's College London
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

use std::collections::HashMap;
use std::convert::{AsRef, TryFrom};
use std::env::{current_dir, var};
use std::error::Error;
use std::fmt::Debug;
use std::fs;
use std::fs::{File, read_to_string};
use std::io;
use std::io::Write;
use std::path::{Path, PathBuf};

use filetime::FileTime;
use typename::TypeName;

use lexer::LexerDef;
use parser::parse_lex;

const RUST_FILE_EXT: &str = "rs";

/// This is a convenience function around [`process_file`](fn.process_file.html) which makes it
/// easier to compile `.l` files stored in a project's `src/` directory. Given the filename `x.l`
/// as input, it will statically compile the file `src/x.l` into a Rust module which can then be
/// imported using `lrlex_mod!(x)`, with the module exposing a function `lexerdef()` which returns a
/// [`LexerDef`](struct.LexerDef.html) that can then be used as normal. Note that leaf names must
/// be unique within a single project, even if they are in different directories: in other words,
/// `a.l` and `x/a.l` will be both mapped to the same file (and it is undefined what the resulting
/// Rust module will contain).
pub fn process_file_in_src<TokId>(srcp: &str,
                                  _terms_map: Option<HashMap<&str, TokId>>)
                               -> Result<(), Box<Error>>
                            where TokId: Copy + Debug + Eq + TryFrom<usize> + TypeName
{
    let mut inp = current_dir()?;
    inp.push("src");
    inp.push(srcp);
    let mut outp = PathBuf::new();
    outp.push(var("OUT_DIR").unwrap());
    outp.push(inp.file_name().unwrap());
    outp.set_extension(RUST_FILE_EXT);
    process_file::<TokId, _, _>(inp, outp)
}

/// Statically compile the `.l` file `inp` into Rust, placing the output into `outp`. The latter
/// defines a module with a function `lexerdef()`, which returns a
/// [`LexerDef`](struct.LexerDef.html) that can then be used as normal
pub fn process_file<TokId, P, Q>(inp: P,
                                 outp: Q)
                              -> Result<(), Box<Error>>
                           where TokId: Copy + Debug + Eq + TryFrom<usize> + TypeName,
                                 P: AsRef<Path>,
                                 Q: AsRef<Path>
{
    if let Ok(outmd) = fs::metadata(&outp) {
        if let Ok(inmd) = fs::metadata(&inp) {
            if FileTime::from_last_modification_time(&outmd) >
               FileTime::from_last_modification_time(&inmd) {
                // The output file already exists, and with a newer timestamp than the input file,
                // so there's no point regenerating the output.
                return Ok(());
            }
        }
    }
    let inc = read_to_string(&inp).unwrap();
    let lexerdef = parse_lex::<TokId>(&inc)?;
    let mut f = File::create(outp)?;
    let mod_name = inp.as_ref().file_stem().unwrap().to_str().unwrap();
    write!(f, "mod {} {{", mod_name)?;
    lexerdef.rust_pp(&mut f)?;
    write!(f, "}}")?;
    Ok(())
}

impl<TokId: Copy + Debug + Eq + TypeName> LexerDef<TokId> {
    pub(crate) fn rust_pp(&self, f: &mut File) -> Result<(), io::Error> {
        // Header
        write!(f, "use lrlex::{{LexerDef, Rule}};

pub fn lexerdef() -> LexerDef<{}> {{
    let rules = vec![", TokId::type_name())?;

        // Individual rules
        for r in &self.rules {
            let tok_id = match r.tok_id {
                Some(ref t) => format!("Some({:?})", t),
                None => "None".to_owned()
            };
            let n = match r.name {
                Some(ref n) => format!("Some({:?}.to_string())", n),
                None => "None".to_owned()
            };
            write!(f, "
Rule::new({}, {}, \"{}\".to_string()).unwrap(),",
                tok_id, n, r.re_str.replace("\\", "\\\\").replace("\"", "\\\""))?;
        }

        // Footer
        write!(f, "
];
    LexerDef::new(rules)
}}")?;
        Ok(())
    }
}
