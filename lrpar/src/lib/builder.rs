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
use std::fs::{File, read_to_string};
use std::hash::Hash;
use std::io::Write;
use std::path::{Path, PathBuf};

use cfgrammar::yacc::{YaccGrammar, YaccKind};
use lrtable::{Minimiser, from_yacc, StateGraph, StateTable};
use num_traits::{PrimInt, Unsigned};
use rmps::{Deserializer, Serializer};
use serde::{Deserialize, Serialize};
use typename::TypeName;

const YACC_SUFFIX: &str = "_y";
const YACC_FILE_EXT: &str = "y";
const RUST_FILE_EXT: &str = "rs";

/// Given the filename `x.y` as input, it will statically compile the file `src/x.y` into a Rust
/// module which can then be imported using `lrpar_mod!(x_y)`. This is a convenience function
/// around [`process_file`](fn.process_file.html) which makes it easier to compile `.y` files
/// stored in a project's `src/` directory. Note that leaf names must be unique within a single
/// project, even if they are in different directories: in other words, `a.y` and `x/a.y` will both
/// be mapped to the same module `a_y` (and it is undefined what the resulting Rust module will
/// contain).
///
/// # Panics
///
/// If the input filename does not end in `.y`.
pub fn process_file_in_src<StorageT, TokId>(srcp: &str)
                                         -> Result<(HashMap<String, TokId>), Box<Error>>
                                      where StorageT: Debug + Hash + PrimInt + TypeName + Unsigned,
                                            TokId: Copy + Debug + Eq + TryFrom<usize> + TypeName
{
    let mut inp = current_dir()?;
    inp.push("src");
    inp.push(srcp);
    if Path::new(srcp).extension().unwrap().to_str().unwrap() != YACC_FILE_EXT {
        panic!("File name passed to process_file_in_src must have extension '{}'.", YACC_FILE_EXT);
    }
    let mut leaf = inp.file_stem().unwrap().to_str().unwrap().to_owned();
    leaf.push_str(&YACC_SUFFIX);
    let mut outp = PathBuf::new();
    outp.push(var("OUT_DIR").unwrap());
    outp.push(leaf);
    outp.set_extension(RUST_FILE_EXT);
    process_file::<StorageT, TokId, _, _>(inp, outp)
}

/// Statically compile the `.y` file `inp` into Rust, placing the output into `outp`. The latter
/// defines a module with the following function:
/// ```rust,ignore
///      parser(lexemes: &Vec<Lexeme<TokId>>)
///   -> Result<Node<TokId>,
///            (Option<Node<TokId>>, Vec<ParseError<TokId>>)>
/// ```
pub fn process_file<StorageT, TokId, P, Q>(inp: P,
                                 outp: Q)
                              -> Result<(HashMap<String, TokId>), Box<Error>>
                           where StorageT: Debug + Hash + PrimInt + TypeName + Unsigned,
                                 TokId: Copy + Debug + Eq + TryFrom<usize> + TypeName,
                                 P: AsRef<Path>,
                                 Q: AsRef<Path>
{
    let inc = read_to_string(&inp).unwrap();

    let grm = match YaccGrammar::new(YaccKind::Eco, &inc) {
        Ok(x) => x,
        Err(s) => {
            panic!("{:?}", s);
        }
    };
    let rule_ids = grm.terms_map().iter()
                                  .map(|(&n, &i)| (n.to_owned(),
                                                   TokId::try_from(usize::from(i))
                                                         .unwrap_or_else(|_| panic!("woo"))))
                                  .collect::<HashMap<_, _>>();

    let (sgraph, stable) = match from_yacc(&grm, Minimiser::Pager) {
        Ok(x) => x,
        Err(s) => {
            panic!("{:?}", s);
        }
    };

    let mut outs = String::new();
    // Header
    let mod_name = inp.as_ref().file_stem().unwrap().to_str().unwrap();
    outs.push_str(&format!("mod {}_y {{", mod_name));
    outs.push_str(&format!("use lrpar::{{Node, parse_rcvry, ParseError, reconstitute, RecoveryKind}};
use lrlex::Lexeme;

pub fn parse(lexemes: &Vec<Lexeme<{tn}>>)
          -> Result<Node<{storaget}, {tn}>, (Option<Node<{storaget}, {tn}>>, Vec<ParseError<{storaget}, {tn}>>)>
{{", storaget=StorageT::type_name(), tn=TokId::type_name()));

    // grm, sgraph, stable
    let mut grm_buf = Vec::new();
    grm.serialize(&mut Serializer::new(&mut grm_buf)).unwrap();
    let mut sgraph_buf = Vec::new();
    sgraph.serialize(&mut Serializer::new(&mut sgraph_buf)).unwrap();
    let mut stable_buf = Vec::new();
    stable.serialize(&mut Serializer::new(&mut stable_buf)).unwrap();
    outs.push_str(&format!("
    let (grm, sgraph, stable) = reconstitute(&vec!{:?}, &vec!{:?}, &vec!{:?});
    parse_rcvry(RecoveryKind::MF, &grm, |_| 1, &sgraph, &stable, lexemes)
", grm_buf, sgraph_buf, stable_buf));

    outs.push_str("}");

    // Footer
    outs.push_str("}");
    // If the file we're about to write out already exists with the same contents, then we don't
    // overwrite it (since that will force a recompile of the file, and relinking of the binary
    // etc).
    if let Ok(curs) = read_to_string(&outp) {
        if curs == outs {
            return Ok(rule_ids);
        }
    }
    let mut f = File::create(outp)?;
    f.write_all(outs.as_bytes())?;
    Ok(rule_ids)
}

/// This function is called by generated files; it exists so that generated files don't require a
/// dependency on serde and rmps.
#[doc(hidden)]
pub fn reconstitute<'a, StorageT: Deserialize<'a> + Hash + PrimInt + Unsigned>
                   (grm_buf: &[u8], sgraph_buf: &[u8], stable_buf: &[u8])
                -> (YaccGrammar<StorageT>, StateGraph<StorageT>, StateTable<StorageT>)
{
    let mut grm_de = Deserializer::new(&grm_buf[..]);
    let grm = Deserialize::deserialize(&mut grm_de).unwrap();
    let mut sgraph_de = Deserializer::new(&sgraph_buf[..]);
    let sgraph = Deserialize::deserialize(&mut sgraph_de).unwrap();
    let mut stable_de = Deserializer::new(&stable_buf[..]);
    let stable = Deserialize::deserialize(&mut stable_de).unwrap();
    (grm, sgraph, stable)
}
