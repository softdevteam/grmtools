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
use std::convert::AsRef;
use std::env::{current_dir, var};
use std::error::Error;
use std::fmt::Debug;
use std::fs::{self, File, read_to_string};
use std::hash::Hash;
use std::io::Write;
use std::marker::PhantomData;
use std::path::{Path, PathBuf};

use bincode::{deserialize, serialize_into};
use cfgrammar::Grammar;
use cfgrammar::yacc::{YaccGrammar, YaccKind};
use filetime::FileTime;
use lrtable::{Minimiser, from_yacc, StateGraph, StateTable};
use num_traits::{AsPrimitive, PrimInt, Unsigned};
use serde::{Deserialize, Serialize};
use typename::TypeName;

use RecoveryKind;

const YACC_SUFFIX: &str = "_y";

const GRM_FILE_EXT: &str = "grm";
const RUST_FILE_EXT: &str = "rs";
const SGRAPH_FILE_EXT: &str = "sgraph";
const STABLE_FILE_EXT: &str = "stable";

/// A `ParserBuilder` allows one to specify the criteria for building a statically generated
/// parser.
pub struct ParserBuilder<StorageT=u32> {
    recoverer: RecoveryKind,
    phantom: PhantomData<StorageT>
}

impl<StorageT> ParserBuilder<StorageT>
where StorageT: 'static + Debug + Hash + PrimInt + Serialize + TypeName + Unsigned,
      usize: AsPrimitive<StorageT>
{
    /// Create a new `ParserBuilder`.
    ///
    /// `StorageT` must be an unsigned integer type (e.g. `u8`, `u16`) which is big enough to index
    /// (separately) all the tokens, nonterminals, and productions in the grammar and less than or
    /// equal in size to `usize` (e.g. on a 64-bit machine `u128` would be too big). In other
    /// words, if you have a grammar with 256 tokens, 256 nonterminals, and 256 productions, you
    /// can safely specify `u8` here; but if any of those counts becomes 256 you will need to
    /// specify `u16`. If you are parsing large files, the additional storage requirements of
    /// larger integer types can be noticeable, and in such cases it can be worth specifying a
    /// smaller type. `StorageT` defaults to `u32` if unspecified.
    ///
    /// # Examples
    ///
    /// ```rust,ignore
    /// ParserBuilder::<u8>::new()
    ///     .process_file_in_src("grm.y")
    ///     .unwrap();
    /// ```
    pub fn new() -> Self {
        ParserBuilder{
            recoverer: RecoveryKind::MF,
            phantom: PhantomData
        }
    }

    /// Set the recoverer for this parser to `rk`.
    pub fn recoverer(mut self, rk: RecoveryKind) -> Self {
        self.recoverer = rk;
        self
    }

    /// Given the filename `x/y.z` as input, statically compile the grammar `src/x/y.z` into a Rust
    /// module which can then be imported using `lrpar_mod!(x_y)`. This is a convenience function
    /// around [`process_file`](struct.ParserBuilder.html#method.process_file) which makes it
    /// easier to compile `.y` files stored in a project's `src/` directory. Note that leaf names
    /// must be unique within a single project, even if they are in different directories: in other
    /// words, `y.z` and `x/y.z` will both be mapped to the same module `y_z` (and it is undefined
    /// which of the input files will "win" the compilation race).
    ///
    /// # Panics
    ///
    /// If `StorageT` is not big enough to index the grammar's tokens, nonterminals, or
    /// productions.
    pub fn process_file_in_src(&self, srcp: &str)
                            -> Result<(HashMap<String, StorageT>), Box<Error>>
    {
        let mut inp = current_dir()?;
        inp.push("src");
        inp.push(srcp);
        let mut outd = PathBuf::new();
        outd.push(var("OUT_DIR").unwrap());
        self.process_file(inp, outd)
    }

    /// Statically compile the Yacc file `inp` into Rust, placing the output file(s) into
    /// the directory `outd`. The latter defines a module with the following function:
    ///
    /// ```rust,ignore
    ///      parser(lexemes: &Vec<Lexeme<StorageT>>)
    ///   -> Result<Node<StorageT>,
    ///            (Option<Node<StorageT>>, Vec<ParseError<StorageT>>)>
    /// ```
    ///
    /// # Panics
    ///
    /// If `StorageT` is not big enough to index the grammar's tokens, nonterminals, or
    /// productions.
    pub fn process_file<P, Q>(&self,
                              inp: P,
                              outd: Q)
                           -> Result<(HashMap<String, StorageT>), Box<Error>>
                        where P: AsRef<Path>,
                              Q: AsRef<Path>
    {
        let inc = read_to_string(&inp).unwrap();
        let grm = YaccGrammar::<StorageT>::new_with_storaget(YaccKind::Eco, &inc)?;
        let rule_ids = grm.terms_map().iter()
                                      .map(|(&n, &i)| (n.to_owned(), i.as_storaget()))
                                      .collect::<HashMap<_, _>>();
        let imc = self.gen_ids_map_cache(&grm);

        // out_base is the base filename for the output (e.g. /path/to/target/out/grm_y) to which
        // we will write filenames with various extensions below.
        let mut outp_base = outd.as_ref().to_path_buf();
        let mut leaf = inp.as_ref().file_stem().unwrap().to_str().unwrap().to_owned();
        leaf.push_str(YACC_SUFFIX);
        outp_base.push(leaf);

        let mut outp_rs = outp_base.clone();
        outp_rs.set_extension(RUST_FILE_EXT);
        // We don't need to go through the full rigmarole of generating an output file if all of
        // the following are true: the output file exists; it is newer than the input file; and the
        // rule IDs map cache hasn't changed. The last of these might be surprising, but it's
        // vital: we don't know what the IDs map might be from one run to the next, and it might
        // change for reasons beyond lrpar's control. If it does change, that means that the lexer
        // and lrpar would get out of sync, so we have to play it safe and regenerate in such cases.
        if let Ok(ref inmd) = fs::metadata(&inp) {
            if let Ok(ref out_rs_md) = fs::metadata(&outp_rs) {
                if FileTime::from_last_modification_time(out_rs_md) >
                   FileTime::from_last_modification_time(inmd) {
                    if let Ok(outc) = read_to_string(&outp_rs) {
                        if outc.contains(&imc) {
                            return Ok(rule_ids);
                        }
                    }
                }
            }
        }

        // At this point, we know we're going to generate fresh output; however, if something goes
        // wrong in the process between now and us writing /out/blah.rs, rustc thinks that
        // everything's gone swimmingly (even if build.rs errored!), and tries to carry on
        // compilation, leading to weird errors. We therefore delete /out/blah.rs at this point,
        // which means, at worse, the user gets a "file not found" error from rustc (which is less
        // confusing than the alternatives).
        fs::remove_file(&outp_rs).ok();

        let (sgraph, stable) = from_yacc(&grm, Minimiser::Pager)?;
        // Because we're lazy, we don't write our own serializer. We use serde and bincode to
        // create files $out_base.grm, $out_base.sgraph, and $out_base.out_stable which contain
        // binary versions of the relevant structs, and then include those binary files into the
        // Rust binary using "include_bytes" (see below).
        let out_grm = self.bin_output(&outp_base, GRM_FILE_EXT, &grm)?;
        let out_sgraph = self.bin_output(&outp_base, SGRAPH_FILE_EXT, &sgraph)?;
        let out_stable = self.bin_output(&outp_base, STABLE_FILE_EXT, &stable)?;

        let mut outs = String::new();
        // Header
        let mod_name = inp.as_ref().file_stem().unwrap().to_str().unwrap();
        outs.push_str(&format!("mod {}_y {{", mod_name));
        outs.push_str(&format!("use lrpar::{{Node, parse_rcvry, ParseError, reconstitute, RecoveryKind}};
use lrlex::Lexeme;

pub fn parse(lexemes: &[Lexeme<{storaget}>])
          -> Result<Node<{storaget}>, (Option<Node<{storaget}>>, Vec<ParseError<{storaget}>>)>
{{", storaget=StorageT::type_name()));

        // grm, sgraph, stable
        let recoverer = match self.recoverer {
            RecoveryKind::CPCTPlus => "CPCTPlus",
            RecoveryKind::MF => "MF",
            RecoveryKind::None => "None"
        };
        outs.push_str(&format!("
    let (grm, sgraph, stable) = reconstitute(include_bytes!(\"{}\"),
                                             include_bytes!(\"{}\"),
                                             include_bytes!(\"{}\"));
    parse_rcvry(RecoveryKind::{}, &grm, |_| 1, &sgraph, &stable, lexemes)
", out_grm.to_str().unwrap(), out_sgraph.to_str().unwrap(), out_stable.to_str().unwrap(), recoverer));

        outs.push_str("}\n");

        // Footer
        outs.push_str("}\n\n");
        // Output the cache so that we can check whether the IDs map is stable.
        outs.push_str(&imc);

        let mut f = File::create(outp_rs)?;
        f.write_all(outs.as_bytes())?;
        Ok(rule_ids)
    }

    /// Generate the rule IDs map cache. We don't need to be particularly clever here: we just need
    /// to record the identifiers and nonterminal names so that we can check if they've changed
    /// later.
    fn gen_ids_map_cache(&self, grm: &YaccGrammar<StorageT>) -> String {
        let mut cache = String::new();
        cache.push_str(" \n/* CACHE INFORMATION\n");
        for tidx in grm.iter_tidxs() {
            let n = match grm.term_name(tidx) {
                Some(n) => format!("'{}'", n),
                None => format!("<unknown>")
            };
            cache.push_str(&format!("   {} {}\n", usize::from(tidx), n));
        }
        cache.push_str("*/\n");
        cache
    }

    /// Output the structure `d` to the file `outp_base.ext`.
    fn bin_output<P: AsRef<Path>, T: Serialize>
                 (&self, outp_base: P, ext: &str, d: &T)
               -> Result<PathBuf, Box<Error>> {
        let mut outp = outp_base.as_ref().to_path_buf();
        outp.set_extension(ext);
        let f = File::create(&outp)?;
        serialize_into(f, d)?;
        Ok(outp)
    }
}

/// This function is called by generated files; it exists so that generated files don't require a
/// dependency on serde and rmps.
#[doc(hidden)]
pub fn reconstitute<'a, StorageT: Deserialize<'a> + Hash + PrimInt + Unsigned>
                   (grm_buf: &'a [u8], sgraph_buf: &'a [u8], stable_buf: &'a [u8])
                -> (YaccGrammar<StorageT>, StateGraph<StorageT>, StateTable<StorageT>)
{
    let grm = deserialize(grm_buf).unwrap();
    let sgraph = deserialize(sgraph_buf).unwrap();
    let stable = deserialize(stable_buf).unwrap();
    (grm, sgraph, stable)
}
