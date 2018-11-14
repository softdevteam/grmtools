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

use std::{
    collections::HashMap,
    convert::AsRef,
    env::{current_dir, var},
    error::Error,
    fmt::Debug,
    fs::{self, read_to_string, File},
    hash::Hash,
    io::Write,
    marker::PhantomData,
    path::{Path, PathBuf}
};

use bincode::{deserialize, serialize_into};
use cfgrammar::yacc::{YaccGrammar, YaccKind};
use cfgrammar::Symbol;
use filetime::FileTime;
use lrtable::{from_yacc, Minimiser, StateGraph, StateTable};
use num_traits::{AsPrimitive, PrimInt, Unsigned};
use serde::{Deserialize, Serialize};
use typename::TypeName;
use regex::Regex;

use RecoveryKind;

const YACC_SUFFIX: &str = "_y";
const ACTION_PREFIX: &str = "__gt_";

const GRM_FILE_EXT: &str = "grm";
const RUST_FILE_EXT: &str = "rs";
const SGRAPH_FILE_EXT: &str = "sgraph";
const STABLE_FILE_EXT: &str = "stable";


/// By default `CTParserBuilder` generates a parse tree which is returned after a successful parse.
/// If the user wants to supply custom actions to be executed during reductions and return their
/// results, they may change `ActionKind` to `CustomAction` instead.
pub enum ActionKind {
    CustomAction,
    GenericParseTree
}

/// A `CTParserBuilder` allows one to specify the criteria for building a statically generated
/// parser.
pub struct CTParserBuilder<StorageT = u32> {
    // Anything stored in here almost certainly needs to be included as part of the rebuild_cache
    // function below so that, if it's changed, the grammar is rebuilt.
    recoverer: RecoveryKind,
    phantom: PhantomData<StorageT>,
    actionkind: ActionKind
}

impl<StorageT> CTParserBuilder<StorageT>
where
    StorageT: 'static + Debug + Hash + PrimInt + Serialize + TypeName + Unsigned,
    usize: AsPrimitive<StorageT>,
    u32: AsPrimitive<StorageT>
{
    /// Create a new `CTParserBuilder`.
    ///
    /// `StorageT` must be an unsigned integer type (e.g. `u8`, `u16`) which is big enough to index
    /// (separately) all the tokens, rules, and productions in the grammar and less than or
    /// equal in size to `usize` (e.g. on a 64-bit machine `u128` would be too big). In other
    /// words, if you have a grammar with 256 tokens, 256 rules, and 256 productions, you
    /// can safely specify `u8` here; but if any of those counts becomes 256 you will need to
    /// specify `u16`. If you are parsing large files, the additional storage requirements of
    /// larger integer types can be noticeable, and in such cases it can be worth specifying a
    /// smaller type. `StorageT` defaults to `u32` if unspecified.
    ///
    /// # Examples
    ///
    /// ```rust,ignore
    /// CTParserBuilder::<u8>::new()
    ///     .process_file_in_src("grm.y")
    ///     .unwrap();
    /// ```
    pub fn new() -> Self {
        CTParserBuilder {
            recoverer: RecoveryKind::MF,
            phantom: PhantomData,
            actionkind: ActionKind::GenericParseTree
        }
    }

    /// Set the recoverer for this parser to `rk`.
    pub fn recoverer(mut self, rk: RecoveryKind) -> Self {
        self.recoverer = rk;
        self
    }

    /// Given the filename `x/y.z` as input, statically compile the grammar `src/x/y.z` into a Rust
    /// module which can then be imported using `lrpar_mod!(x_y)`. This is a convenience function
    /// around [`process_file`](struct.CTParserBuilder.html#method.process_file) which makes it
    /// easier to compile `.y` files stored in a project's `src/` directory. Note that leaf names
    /// must be unique within a single project, even if they are in different directories: in other
    /// words, `y.z` and `x/y.z` will both be mapped to the same module `y_z` (and it is undefined
    /// which of the input files will "win" the compilation race).
    ///
    /// # Panics
    ///
    /// If `StorageT` is not big enough to index the grammar's tokens, rules, or
    /// productions.
    pub fn process_file_in_src(
        &self,
        srcp: &str
    ) -> Result<(HashMap<String, StorageT>), Box<Error>> {
        let mut inp = current_dir()?;
        inp.push("src");
        inp.push(srcp);
        let mut outd = PathBuf::new();
        outd.push(var("OUT_DIR").unwrap());
        self.process_file(inp, outd)
    }

    pub fn action_kind(mut self, ak: ActionKind) -> Self {
        self.actionkind = ak;
        self
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
    /// If `StorageT` is not big enough to index the grammar's tokens, rules, or
    /// productions.
    pub fn process_file<P, Q>(
        &self,
        inp: P,
        outd: Q
    ) -> Result<(HashMap<String, StorageT>), Box<Error>>
    where
        P: AsRef<Path>,
        Q: AsRef<Path>
    {
        let inc = read_to_string(&inp).unwrap();
        let grm = YaccGrammar::<StorageT>::new_with_storaget(YaccKind::Eco, &inc)?;
        let rule_ids = grm
            .tokens_map()
            .iter()
            .map(|(&n, &i)| (n.to_owned(), i.as_storaget()))
            .collect::<HashMap<_, _>>();
        let cache = self.rebuild_cache(&grm);

        // out_base is the base filename for the output (e.g. /path/to/target/out/grm_y) to which
        // we will write filenames with various extensions below.
        let mut outp_base = outd.as_ref().to_path_buf();
        let mut leaf = inp
            .as_ref()
            .file_stem()
            .unwrap()
            .to_str()
            .unwrap()
            .to_owned();
        leaf.push_str(YACC_SUFFIX);
        outp_base.push(leaf);

        let mut outp_rs = outp_base.clone();
        outp_rs.set_extension(RUST_FILE_EXT);
        // We don't need to go through the full rigmarole of generating an output file if all of
        // the following are true: the output file exists; it is newer than the input file; and the
        // cache hasn't changed. The last of these might be surprising, but it's vital: we don't
        // know, for example, what the IDs map might be from one run to the next, and it might
        // change for reasons beyond lrpar's control. If it does change, that means that the lexer
        // and lrpar would get out of sync, so we have to play it safe and regenerate in such
        // cases.
        if let Ok(ref inmd) = fs::metadata(&inp) {
            if let Ok(ref out_rs_md) = fs::metadata(&outp_rs) {
                if FileTime::from_last_modification_time(out_rs_md)
                    > FileTime::from_last_modification_time(inmd)
                {
                    if let Ok(outc) = read_to_string(&outp_rs) {
                        if outc.contains(&cache) {
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
        outs.push_str(&format!("mod {}_y {{\n", mod_name));
        outs.push_str("    use lrpar::{{Lexer, Node, LexParseError, RecoveryKind, RTParserBuilder}};
    use lrpar::ctbuilder::_reconstitute;",
        );

        match self.actionkind {
            ActionKind::CustomAction => {
                outs.push_str(&format!("use lrpar::parser::AStackType;

    pub fn parse(lexer: &mut Lexer<{storaget}>)
          -> Result<TYPE, LexParseError<{storaget}>>
    {{",
                storaget = StorageT::type_name()
                ));
            }
            ActionKind::GenericParseTree => {
                outs.push_str(&format!("
    pub fn parse(lexer: &mut Lexer<{storaget}>)
          -> Result<Node<{storaget}>, LexParseError<{storaget}>>
    {{",
                storaget = StorageT::type_name()
                ));
            }
        };

        // grm, sgraph, stable
        let recoverer = match self.recoverer {
            RecoveryKind::CPCTPlus => "CPCTPlus",
            RecoveryKind::MF => "MF",
            RecoveryKind::Panic => "Panic",
            RecoveryKind::None => "None"
        };

        outs.push_str(&format!("
        let (grm, sgraph, stable) = _reconstitute(include_bytes!(\"{}\"),
                                                  include_bytes!(\"{}\"),
                                                  include_bytes!(\"{}\"));",
                out_grm.to_str().unwrap(),
                out_sgraph.to_str().unwrap(),
                out_stable.to_str().unwrap()));

        match self.actionkind {
            ActionKind::CustomAction => {
                // action function references
                outs.push_str(&format!("\n        let mut actions: Vec<Option<&Fn(&str, Vec<AStackType<TYPE, {}>>) -> TYPE>> = Vec::new();\n", StorageT::type_name()));
                for pidx in grm.iter_pidxs() {
                    if grm.action(pidx).is_some() {
                        outs.push_str(&format!("        actions.push(Some(&{prefix}action_{}));\n", usize::from(pidx), prefix=ACTION_PREFIX))
                    }
                    else {
                        outs.push_str("        actions.push(None);")
                    };
                }
                outs.push_str(&format!("
        let s = lexer.input().to_string();
        RTParserBuilder::new(&grm, &sgraph, &stable)
            .recoverer(RecoveryKind::{})
            .parse2(lexer, actions, &s)\n",
                recoverer,
                ));
            },
            ActionKind::GenericParseTree => {
                outs.push_str(&format!("
        RTParserBuilder::new(&grm, &sgraph, &stable)
            .recoverer(RecoveryKind::{})
            .parse(lexer)\n",
                recoverer
                ));
            }
        };

        outs.push_str("    }\n\n");

        // The rule constants
        for ridx in grm.iter_rules() {
            if !grm.rule_to_prods(ridx).contains(&grm.start_prod()) {
                outs.push_str(&format!(
                    "    #[allow(dead_code)]\n    pub const R_{}: {} = {:?};\n",
                    grm.rule_name(ridx).to_ascii_uppercase(),
                    StorageT::type_name(),
                    usize::from(ridx)
                ));
            }
        }

        match self.actionkind {
            ActionKind::CustomAction => {
                let re: Regex = { Regex::new(r"\$([0-9]+)").unwrap() };
                if let Some(s) = grm.programs() {
                    outs.push_str("\n/* User code */\n\n");
                    outs.push_str(s);
                }

                // Convert actions to functions
                outs.push_str("\n/* Converted actions */\n\n");
                for pidx in grm.iter_pidxs() {
                    if let Some(s) = grm.action(pidx) {
                        // Iterate over all $-arguments and replace them with their respective
                        // element from the argument vector (e.g. $1 is replaced by args[0]). At
                        // the same time extract &str from tokens and usertype from nonterminals.
                        outs.push_str(&format!("fn {prefix}action_{}({prefix}input: &str, {prefix}args: Vec<AStackType<TYPE, {}>>) -> TYPE {{\n", usize::from(pidx), StorageT::type_name(), prefix=ACTION_PREFIX));
                        for m in re.find_iter(s) {
                            let num = match &s[m.start()+1..m.end()].parse::<usize>() {
                                Ok(val) => val - 1,
                                Err(_) => unreachable!()
                            };
                            outs.push_str(&format!("    let {prefix}arg_{} = match {prefix}args[{}] {{", num+1, num, prefix=ACTION_PREFIX));
                            match grm.prod(pidx)[num] {
                                Symbol::Rule(_) => {
                                    outs.push_str("
        AStackType::ActionType(v) => v,
        AStackType::Lexeme(_) => unreachable!()
    };
")
                                },
                                Symbol::Token(_) => {
                                    outs.push_str(&format!("
        AStackType::ActionType(_) => unreachable!(),
        AStackType::Lexeme(l) => &{prefix}input[l.start()..l.end()]
    }};
", prefix=ACTION_PREFIX))
                                }
                            };
                        }
                        let ns = re.replace_all(s, format!("{prefix}arg_$1", prefix=ACTION_PREFIX).as_str());
                        outs.push_str(&format!("    {}", &ns, ));
                        outs.push_str("\n}\n\n");
                    }
                }
            },
            ActionKind::GenericParseTree => ()
        };

        outs.push_str("}\n\n");

        // Output the cache so that we can check whether the IDs map is stable.
        outs.push_str(&cache);

        let mut f = File::create(outp_rs)?;
        f.write_all(outs.as_bytes())?;
        Ok(rule_ids)
    }

    /// Generate the cache, which determines if anything's changed enough that we need to
    /// regenerate outputs and force rustc to recompile.
    fn rebuild_cache(&self, grm: &YaccGrammar<StorageT>) -> String {
        // We don't need to be particularly clever here: we just need to record the various things
        // that could change between builds.
        let mut cache = String::new();
        cache.push_str("\n/* CACHE INFORMATION\n");

        // Record the time that this version of lrpar was built. If the source code changes and
        // rustc forces a recompile, this will change this value, causing anything which depends on
        // this build of lrpar to be recompiled too.
        cache.push_str(&format!(
            "   Build time: {:?}",
            env!("VERGEN_BUILD_TIMESTAMP")
        ));

        // Record the recoverer
        cache.push_str(&format!("   Recoverer: {:?}\n", self.recoverer));

        // Record the rule IDs map
        for tidx in grm.iter_tidxs() {
            let n = match grm.token_name(tidx) {
                Some(n) => format!("'{}'", n),
                None => format!("<unknown>")
            };
            cache.push_str(&format!("   {} {}\n", usize::from(tidx), n));
        }

        cache.push_str("*/\n");
        cache
    }

    /// Output the structure `d` to the file `outp_base.ext`.
    fn bin_output<P: AsRef<Path>, T: Serialize>(
        &self,
        outp_base: P,
        ext: &str,
        d: &T
    ) -> Result<PathBuf, Box<Error>> {
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
pub fn _reconstitute<'a, StorageT: Deserialize<'a> + Hash + PrimInt + Unsigned>(
    grm_buf: &'a [u8],
    sgraph_buf: &'a [u8],
    stable_buf: &'a [u8]
) -> (
    YaccGrammar<StorageT>,
    StateGraph<StorageT>,
    StateTable<StorageT>
) {
    let grm = deserialize(grm_buf).unwrap();
    let sgraph = deserialize(sgraph_buf).unwrap();
    let stable = deserialize(stable_buf).unwrap();
    (grm, sgraph, stable)
}
