// Copyright (c) 2018 King's College London
// created by the Software Development Team <http://soft-dev.org/>
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0>, or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, or the UPL-1.0 license <http://opensource.org/licenses/UPL>
// at your option. This file may not be copied, modified, or distributed except according to those
// terms.

use std::{
    collections::HashMap,
    convert::AsRef,
    env::{current_dir, var},
    error::Error,
    fmt::{self, Debug},
    fs::{self, read_to_string, File},
    hash::Hash,
    io::Write,
    marker::PhantomData,
    path::{Path, PathBuf}
};

use bincode::{deserialize, serialize_into};
use cfgrammar::{
    yacc::{YaccGrammar, YaccKind, YaccOriginalActionKind},
    RIdx, Symbol
};
use filetime::FileTime;
use lazy_static::lazy_static;
use lrtable::{from_yacc, statetable::Conflicts, Minimiser, StateGraph, StateTable};
use num_traits::{AsPrimitive, PrimInt, Unsigned};
use regex::Regex;
use serde::{Deserialize, Serialize};
use typename::TypeName;

use crate::RecoveryKind;

const YACC_SUFFIX: &str = "_y";
const ACTION_PREFIX: &str = "__gt_";
const GLOBAL_PREFIX: &str = "__GT_";
const ACTIONS_KIND: &str = "__GTActionsKind";
const ACTIONS_KIND_PREFIX: &str = "AK";

const GRM_FILE_EXT: &str = "grm";
const RUST_FILE_EXT: &str = "rs";
const SGRAPH_FILE_EXT: &str = "sgraph";
const STABLE_FILE_EXT: &str = "stable";

lazy_static! {
    static ref RE_DOL_NUM: Regex = Regex::new(r"\$([0-9]+)").unwrap();
    static ref RE_DOL_LEXER: Regex = Regex::new(r"\$lexer").unwrap();
}

struct CTConflictsError<StorageT: Eq + Hash> {
    pub grm: YaccGrammar<StorageT>,
    pub sgraph: StateGraph<StorageT>,
    pub stable: StateTable<StorageT>
}

impl<StorageT> fmt::Display for CTConflictsError<StorageT>
where
    StorageT: 'static + Debug + Hash + PrimInt + Serialize + TypeName + Unsigned,
    usize: AsPrimitive<StorageT>,
    u32: AsPrimitive<StorageT>
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let conflicts = self.stable.conflicts().unwrap();
        write!(
            f,
            "CTConflictsError{{{} Shift/Reduce, {} Reduce/Reduce}}",
            conflicts.sr_len(),
            conflicts.rr_len()
        )
    }
}

impl<StorageT> fmt::Debug for CTConflictsError<StorageT>
where
    StorageT: 'static + Debug + Hash + PrimInt + Serialize + TypeName + Unsigned,
    usize: AsPrimitive<StorageT>,
    u32: AsPrimitive<StorageT>
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let conflicts = self.stable.conflicts().unwrap();
        write!(
            f,
            "CTConflictsError{{{} Shift/Reduce, {} Reduce/Reduce}}",
            conflicts.sr_len(),
            conflicts.rr_len()
        )
    }
}

impl<StorageT> Error for CTConflictsError<StorageT>
where
    StorageT: 'static + Debug + Hash + PrimInt + Serialize + TypeName + Unsigned,
    usize: AsPrimitive<StorageT>,
    u32: AsPrimitive<StorageT>
{
}

/// A `CTParserBuilder` allows one to specify the criteria for building a statically generated
/// parser.
pub struct CTParserBuilder<StorageT = u32>
where
    StorageT: Eq + Hash
{
    // Anything stored in here (except `conflicts` and `error_on_conflict`) almost certainly needs
    // to be included as part of the rebuild_cache function below so that, if it's changed, the
    // grammar is rebuilt.
    recoverer: RecoveryKind,
    phantom: PhantomData<StorageT>,
    yacckind: Option<YaccKind>,
    error_on_conflicts: bool,
    conflicts: Option<(
        YaccGrammar<StorageT>,
        StateGraph<StorageT>,
        StateTable<StorageT>
    )>
}

impl CTParserBuilder<u32> {
    /// Create a new `CTParserBuilder`.
    ///
    /// # Examples
    ///
    /// ```text
    /// CTParserBuilder::new()
    ///     .process_file_in_src("grm.y")
    ///     .unwrap();
    /// ```
    pub fn new() -> Self {
        CTParserBuilder::<u32>::new_with_storaget()
    }
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
    /// ```text
    /// CTParserBuilder::<u8>::new_with_storaget()
    ///     .process_file_in_src("grm.y")
    ///     .unwrap();
    /// ```
    pub fn new_with_storaget() -> Self {
        CTParserBuilder {
            recoverer: RecoveryKind::MF,
            phantom: PhantomData,
            yacckind: None,
            error_on_conflicts: true,
            conflicts: None
        }
    }

    /// Set the recoverer for this parser to `rk`.
    pub fn recoverer(mut self, rk: RecoveryKind) -> Self {
        self.recoverer = rk;
        self
    }

    /// Given the filename `x/y.z` as input, statically compile the grammar `src/x/y.z` into a Rust
    /// module which can then be imported using `lrpar_mod!(x_y)`. This is a convenience function
    /// around [`process_file`](#method.process_file) which makes it easier to compile `.y` files
    /// stored in a project's `src/` directory.
    ///
    /// Note that leaf names must be unique within a single project, even if they are in different
    /// directories: in other words, `y.z` and `x/y.z` will both be mapped to the same module `y_z`
    /// (and it is undefined which of the input files will "win" the compilation race).
    ///
    /// # Panics
    ///
    /// If `StorageT` is not big enough to index the grammar's tokens, rules, or
    /// productions.
    pub fn process_file_in_src(
        &mut self,
        srcp: &str
    ) -> Result<HashMap<String, StorageT>, Box<Error>> {
        let mut inp = current_dir()?;
        inp.push("src");
        inp.push(srcp);
        let mut outd = PathBuf::new();
        outd.push(var("OUT_DIR").unwrap());
        self.process_file(inp, outd)
    }

    /// Set the `YaccKind` for this parser to `ak`.
    pub fn yacckind(mut self, yk: YaccKind) -> Self {
        self.yacckind = Some(yk);
        self
    }

    /// If set to true, `process_file_in_src` will return an error if the given grammar contains
    /// any Shift/Reduce or Reduce/Reduce conflicts. Defaults to `true`.
    pub fn error_on_conflicts(mut self, b: bool) -> Self {
        self.error_on_conflicts = b;
        self
    }

    /// If there are any conflicts in the grammar, return a tuple which allows users to inspect
    /// and pretty print them; otherwise returns `None`. Note: The conflicts feature is currently
    /// unstable and may change in the future.
    pub fn conflicts(
        &self
    ) -> Option<(
        &YaccGrammar<StorageT>,
        &StateGraph<StorageT>,
        &StateTable<StorageT>,
        &Conflicts<StorageT>
    )> {
        if let Some((grm, sgraph, stable)) = &self.conflicts {
            return Some((grm, sgraph, stable, &stable.conflicts().unwrap()));
        }
        None
    }

    /// Statically compile the Yacc file `inp` into Rust, placing the output file(s) into
    /// the directory `outd`. The latter defines a module with the following functions:
    ///
    /// ```text
    ///    fn parse(lexemes: &Vec<Lexeme<StorageT>>)
    ///         -> (Option<ActionT>, Vec<LexParseError<StorageT>>)>
    ///
    ///    fn token_epp<'a>(tidx: TIdx<StorageT>) -> Option<&'a str>
    /// ```
    ///
    /// Where `ActionT` is either:
    ///
    ///   * the `%actiontype` value given to the grammar
    ///   * or, if the `yacckind` was set YaccKind::Original(YaccOriginalActionKind::UserAction),
    ///     it is [`Node<StorageT>`](../parser/enum.Node.html)
    ///
    /// # Panics
    ///
    /// If `StorageT` is not big enough to index the grammar's tokens, rules, or
    /// productions.
    pub fn process_file<P, Q>(
        &mut self,
        inp: P,
        outd: Q
    ) -> Result<HashMap<String, StorageT>, Box<Error>>
    where
        P: AsRef<Path>,
        Q: AsRef<Path>
    {
        let yk = match self.yacckind {
            None => panic!("yacckind must be specified before processing."),
            Some(YaccKind::Original(x)) => YaccKind::Original(x),
            Some(YaccKind::Grmtools) => YaccKind::Grmtools,
            Some(YaccKind::Eco) => panic!("Eco compile-time grammar generation not supported.")
        };
        let inc = read_to_string(&inp).unwrap();
        let grm = YaccGrammar::<StorageT>::new_with_storaget(yk, &inc)?;
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
        if stable.conflicts().is_some() && self.error_on_conflicts {
            return Err(Box::new(CTConflictsError {
                grm,
                sgraph,
                stable
            }));
        }

        let mod_name = inp.as_ref().file_stem().unwrap().to_str().unwrap();
        self.output_file(&grm, &sgraph, &stable, mod_name, outp_base, outp_rs, &cache)?;
        if stable.conflicts().is_some() {
            self.conflicts = Some((grm, sgraph, stable));
        }
        Ok(rule_ids)
    }

    fn output_file(
        &self,
        grm: &YaccGrammar<StorageT>,
        sgraph: &StateGraph<StorageT>,
        stable: &StateTable<StorageT>,
        mod_name: &str,
        outp_base: PathBuf,
        outp_rs: PathBuf,
        cache: &str
    ) -> Result<(), Box<Error>> {
        let mut outs = String::new();
        // Header
        outs.push_str(&format!("mod {}_y {{\n", mod_name));
        outs.push_str(
            "    use lrpar::{{Lexer, LexParseError, RecoveryKind, RTParserBuilder}};
    use lrpar::ctbuilder::_reconstitute;
    use cfgrammar::TIdx;
"
        );

        outs.push_str(&self.gen_parse_function(grm, sgraph, stable, outp_base)?);
        outs.push_str(&self.gen_rule_consts(grm));
        outs.push_str(&self.gen_token_epp(&grm));
        match self.yacckind.unwrap() {
            YaccKind::Original(YaccOriginalActionKind::UserAction) | YaccKind::Grmtools => {
                outs.push_str(&self.gen_wrappers(&grm));
                outs.push_str(&self.gen_user_actions(&grm));
            }
            YaccKind::Original(YaccOriginalActionKind::NoAction)
            | YaccKind::Original(YaccOriginalActionKind::GenericParseTree) => (),
            _ => unreachable!()
        }
        outs.push_str("}\n\n");

        // Output the cache so that we can check whether the IDs map is stable.
        outs.push_str(&cache);

        let mut f = File::create(outp_rs)?;
        f.write_all(outs.as_bytes())?;

        Ok(())
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
                None => "<unknown>".to_string()
            };
            cache.push_str(&format!("   {} {}\n", usize::from(tidx), n));
        }

        cache.push_str("*/\n");
        cache
    }

    /// Generate the main parse() function for the output file.
    fn gen_parse_function(
        &self,
        grm: &YaccGrammar<StorageT>,
        sgraph: &StateGraph<StorageT>,
        stable: &StateTable<StorageT>,
        outp_base: PathBuf
    ) -> Result<String, Box<Error>> {
        let mut outs = String::new();
        match self.yacckind.unwrap() {
            YaccKind::Original(YaccOriginalActionKind::UserAction) | YaccKind::Grmtools => {
                outs.push_str(&format!(
                    "    use lrpar::{{Lexeme, parser::AStackType}};
    use cfgrammar::RIdx;
    use std::vec;

    pub fn parse(lexer: &mut Lexer<{storaget}>)
          -> (Option<{actiont}>, Vec<LexParseError<{storaget}>>)
    {{",
                    storaget = StorageT::type_name(),
                    actiont = grm.actiontype(self.user_start_ridx(grm)).as_ref().unwrap()
                ));
            }
            YaccKind::Original(YaccOriginalActionKind::GenericParseTree) => {
                outs.push_str(&format!(
                    "use lrpar::Node;

    pub fn parse(lexer: &mut Lexer<{storaget}>)
          -> (Option<Node<{storaget}>>, Vec<LexParseError<{storaget}>>)
    {{",
                    storaget = StorageT::type_name()
                ));
            }
            YaccKind::Original(YaccOriginalActionKind::NoAction) => {
                outs.push_str(&format!(
                    "    pub fn parse(lexer: &mut Lexer<{storaget}>)
          -> Vec<LexParseError<{storaget}>>
    {{",
                    storaget = StorageT::type_name()
                ));
            }
            YaccKind::Eco => unreachable!()
        };

        // Because we're lazy, we don't write our own serializer. We use serde and bincode to
        // create files $out_base.grm, $out_base.sgraph, and $out_base.out_stable which contain
        // binary versions of the relevant structs, and then include those binary files into the
        // Rust binary using "include_bytes" (see below).
        let out_grm = self.bin_output(&outp_base, GRM_FILE_EXT, &grm)?;
        let out_sgraph = self.bin_output(&outp_base, SGRAPH_FILE_EXT, &sgraph)?;
        let out_stable = self.bin_output(&outp_base, STABLE_FILE_EXT, &stable)?;
        outs.push_str(&format!(
            "
        let (grm, sgraph, stable) = _reconstitute(include_bytes!(\"{}\"),
                                                  include_bytes!(\"{}\"),
                                                  include_bytes!(\"{}\"));",
            out_grm.to_str().unwrap(),
            out_sgraph.to_str().unwrap(),
            out_stable.to_str().unwrap()
        ));

        // grm, sgraph, stable
        let recoverer = match self.recoverer {
            RecoveryKind::CPCTPlus => "CPCTPlus",
            RecoveryKind::MF => "MF",
            RecoveryKind::Panic => "Panic",
            RecoveryKind::None => "None"
        };
        match self.yacckind.unwrap() {
            YaccKind::Original(YaccOriginalActionKind::UserAction) | YaccKind::Grmtools => {
                // action function references
                outs.push_str(&format!(
                    "\n        let mut actions: Vec<&Fn(RIdx<{storaget}>,
                       &Lexer<{storaget}>,
                       vec::Drain<AStackType<{actionskind}, {storaget}>>)
                    -> {actionskind}> = Vec::new();\n",
                    actionskind = ACTIONS_KIND,
                    storaget = StorageT::type_name()
                ));
                for pidx in grm.iter_pidxs() {
                    outs.push_str(&format!(
                        "        actions.push(&{prefix}wrapper_{});\n",
                        usize::from(pidx),
                        prefix = ACTION_PREFIX
                    ))
                }
                outs.push_str(&format!(
                    "
        match RTParserBuilder::new(&grm, &sgraph, &stable)
            .recoverer(RecoveryKind::{recoverer})
            .parse_actions(lexer, &actions) {{
                (Some({actionskind}::{actionskindprefix}{ridx}(x)), y) => (Some(x), y),
                (None, y) => (None, y),
                _ => unreachable!()
        }}",
                    actionskind = ACTIONS_KIND,
                    actionskindprefix = ACTIONS_KIND_PREFIX,
                    ridx = usize::from(self.user_start_ridx(grm)),
                    recoverer = recoverer,
                ));
            }
            YaccKind::Original(YaccOriginalActionKind::GenericParseTree) => {
                outs.push_str(&format!(
                    "
        RTParserBuilder::new(&grm, &sgraph, &stable)
            .recoverer(RecoveryKind::{})
            .parse_generictree(lexer)\n",
                    recoverer
                ));
            }
            YaccKind::Original(YaccOriginalActionKind::NoAction) => {
                outs.push_str(&format!(
                    "
        RTParserBuilder::new(&grm, &sgraph, &stable)
            .recoverer(RecoveryKind::{})
            .parse_noaction(lexer)\n",
                    recoverer
                ));
            }
            YaccKind::Eco => unreachable!()
        };

        outs.push_str("\n    }\n\n");
        Ok(outs)
    }

    fn gen_rule_consts(&self, grm: &YaccGrammar<StorageT>) -> String {
        let mut outs = String::new();
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
        outs
    }

    fn gen_token_epp(&self, grm: &YaccGrammar<StorageT>) -> String {
        let mut tidxs = Vec::new();
        for tidx in grm.iter_tidxs() {
            match grm.token_epp(tidx) {
                Some(n) => tidxs.push(format!("Some(\"{}\")", str_escape(n))),
                None => tidxs.push("None".to_string())
            }
        }
        format!(
            "    const {prefix}EPP: &[Option<&str>] = &[{}];

    /// Return the %epp entry for token `tidx` (where `None` indicates \"the token has no
    /// pretty-printed value\"). Panics if `tidx` doesn't exist.
    #[allow(dead_code)]
    pub fn token_epp<'a>(tidx: TIdx<{storaget}>) -> Option<&'a str> {{
        {prefix}EPP[usize::from(tidx)]
    }}",
            tidxs.join(", "),
            storaget = StorageT::type_name(),
            prefix = GLOBAL_PREFIX
        )
    }

    /// Generate the wrappers that call user actions
    fn gen_wrappers(&self, grm: &YaccGrammar<StorageT>) -> String {
        let mut outs = String::new();

        outs.push_str("\n\n    // Wrappers\n\n");

        for pidx in grm.iter_pidxs() {
            let ridx = grm.prod_to_rule(pidx);

            // Iterate over all $-arguments and replace them with their respective
            // element from the argument vector (e.g. $1 is replaced by args[0]). At
            // the same time extract &str from tokens and actiontype from nonterminals.
            outs.push_str(&format!(
                "    fn {prefix}wrapper_{}({prefix}ridx: RIdx<{storaget}>,
                      {prefix}lexer: &Lexer<{storaget}>,
                      mut {prefix}args: vec::Drain<AStackType<{actionskind}, {storaget}>>)
                   -> {actionskind} {{",
                usize::from(pidx),
                storaget = StorageT::type_name(),
                prefix = ACTION_PREFIX,
                actionskind = ACTIONS_KIND,
            ));

            if grm.action(pidx).is_some() {
                // Unpack the arguments passed to us by the drain
                for i in 0..grm.prod(pidx).len() {
                    match grm.prod(pidx)[i] {
                        Symbol::Rule(ref_ridx) => outs.push_str(&format!(
                            "
        let {prefix}arg_{i} = match {prefix}args.next().unwrap() {{
            AStackType::ActionType({actionskind}::{actionskindprefix}{ref_ridx}(x)) => x,
            _ => unreachable!()
        }};",
                            i = i + 1,
                            ref_ridx = usize::from(ref_ridx),
                            prefix = ACTION_PREFIX,
                            actionskind = ACTIONS_KIND,
                            actionskindprefix = ACTIONS_KIND_PREFIX
                        )),
                        Symbol::Token(_) => outs.push_str(&format!(
                            "
        let {prefix}arg_{} = match {prefix}args.next().unwrap() {{
            AStackType::Lexeme(l) => {{
                if l.len().is_some() {{
                    Ok(l)
                }} else {{
                    Err(l)
                }}
            }},
            AStackType::ActionType(_) => unreachable!()
        }};",
                            i + 1,
                            prefix = ACTION_PREFIX
                        ))
                    }
                }

                // Call the user code
                let args = (0..grm.prod(pidx).len())
                    .map(|i| format!("{prefix}arg_{i}", prefix = ACTION_PREFIX, i = i + 1))
                    .collect::<Vec<_>>();
                outs.push_str(&format!("\n        {actionskind}::{actionskindprefix}{ridx}({prefix}action_{pidx}({prefix}ridx, {prefix}lexer, {args}))",
                    actionskind = ACTIONS_KIND,
                    actionskindprefix = ACTIONS_KIND_PREFIX,
                    prefix = ACTION_PREFIX,
                    ridx = usize::from(ridx),
                    pidx = usize::from(pidx),
                    args = args.join(", ")));
            } else if pidx == grm.start_prod() {
                // The action for the start production (i.e. the extra rule/production
                // added by lrpar) will never be executed, so a dummy function is all
                // that's required. We add "unreachable" as a check in case some other
                // detail of lrpar changes in the future.
                outs.push_str("    unreachable!()");
            } else {
                panic!(
                    "Production in rule '{}' must have an action body.",
                    grm.rule_name(grm.prod_to_rule(pidx))
                );
            }
            outs.push_str("\n    }\n\n");
        }

        // Wrappers enum

        outs.push_str(&format!(
            "    #[allow(dead_code)]
    enum {} {{\n",
            ACTIONS_KIND
        ));
        for ridx in grm.iter_rules() {
            if grm.actiontype(ridx).is_none() {
                continue;
            }

            outs.push_str(&format!(
                "        {actionskindprefix}{ridx}({actiont}),\n",
                actionskindprefix = ACTIONS_KIND_PREFIX,
                ridx = usize::from(ridx),
                actiont = grm.actiontype(ridx).as_ref().unwrap()
            ));
        }
        outs.push_str("    }\n\n");

        outs
    }

    /// Generate the user action functions (if any).
    fn gen_user_actions(&self, grm: &YaccGrammar<StorageT>) -> String {
        let mut outs = String::new();

        if let Some(s) = grm.programs() {
            outs.push_str("\n// User code from the program section\n\n");
            outs.push_str(s);
        }

        // Convert actions to functions
        outs.push_str("\n    // User actions\n\n");
        for pidx in grm.iter_pidxs() {
            if pidx == grm.start_prod() {
                continue;
            }

            // Work out the right type for each argument
            let mut args = Vec::with_capacity(grm.prod(pidx).len());
            for i in 0..grm.prod(pidx).len() {
                let argt = match grm.prod(pidx)[i] {
                    Symbol::Rule(ref_ridx) => grm.actiontype(ref_ridx).as_ref().unwrap().clone(),
                    Symbol::Token(_) => format!(
                        "Result<Lexeme<{storaget}>, Lexeme<{storaget}>>",
                        storaget = StorageT::type_name()
                    )
                };
                args.push(format!("mut {}arg_{}: {}", ACTION_PREFIX, i + 1, argt));
            }

            // Iterate over all $-arguments and replace them with their respective
            // element from the argument vector (e.g. $1 is replaced by args[0]). At
            // the same time extract &str from tokens and actiontype from nonterminals.
            outs.push_str(&format!(
                "    fn {prefix}action_{}({prefix}ridx: RIdx<{storaget}>,
                     {prefix}lexer: &Lexer<{storaget}>,
                     {args})
                  -> {actiont} {{\n",
                usize::from(pidx),
                storaget = StorageT::type_name(),
                prefix = ACTION_PREFIX,
                actiont = grm.actiontype(grm.prod_to_rule(pidx)).as_ref().unwrap(),
                args = args.join(",\n                     ")
            ));

            // Replace $1 ... $n with the correct local variable
            let action = grm.action(pidx).as_ref().unwrap();
            let action = RE_DOL_NUM
                .replace_all(
                    &action,
                    format!("{prefix}arg_$1", prefix = ACTION_PREFIX).as_str()
                )
                .into_owned();
            // Replace $lexer with a reference to the lexer variable
            let action = RE_DOL_LEXER.replace_all(
                &action,
                format!("{prefix}lexer", prefix = ACTION_PREFIX).as_str()
            );
            outs.push_str(&action);
            outs.push_str("\n    }\n\n");
        }
        outs
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

    /// Return the `RIdx` of the %start rule in the grammar (which will not be the same as
    /// grm.start_rule_idx because the latter has an additional rule insert by cfgrammar
    /// which then calls the user's %start rule).
    fn user_start_ridx(&self, grm: &YaccGrammar<StorageT>) -> RIdx<StorageT> {
        debug_assert_eq!(grm.prod(grm.start_prod()).len(), 1);
        match grm.prod(grm.start_prod())[0] {
            Symbol::Rule(ridx) => ridx,
            _ => unreachable!()
        }
    }
}

/// Return a version of the string `s` which is safe to embed in source code as a string.
fn str_escape(s: &str) -> String {
    s.replace("\\", "\\\\").replace("\"", "\\\"")
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

#[cfg(test)]
mod test {
    use std::{fs::File, io::Write, path::PathBuf};

    use super::{CTConflictsError, CTParserBuilder};
    use cfgrammar::yacc::{YaccKind, YaccOriginalActionKind};
    use tempfile::TempDir;

    #[test]
    fn test_conflicts() {
        let temp = TempDir::new().unwrap();
        let mut file_path = PathBuf::from(temp.as_ref());
        file_path.push("grm.y");
        let mut f = File::create(&file_path).unwrap();
        let _ = f.write_all(
            "%start A
%%
A : 'a' 'b' | B 'b';
B : 'a' | C;
C : 'a';"
                .as_bytes()
        );

        let mut ct = CTParserBuilder::new()
            .error_on_conflicts(false)
            .yacckind(YaccKind::Original(YaccOriginalActionKind::GenericParseTree));
        ct.process_file_in_src(file_path.to_str().unwrap()).unwrap();

        match ct.conflicts() {
            Some((_, _, _, conflicts)) => {
                assert_eq!(conflicts.sr_len(), 1);
                assert_eq!(conflicts.rr_len(), 1);
            }
            None => panic!("Expected error data")
        }
    }

    #[test]
    fn test_conflicts_error() {
        let temp = TempDir::new().unwrap();
        let mut file_path = PathBuf::from(temp.as_ref());
        file_path.push("grm.y");
        let mut f = File::create(&file_path).unwrap();
        let _ = f.write_all(
            "%start A
%%
A : 'a' 'b' | B 'b';
B : 'a' | C;
C : 'a';"
                .as_bytes()
        );

        match CTParserBuilder::new()
            .yacckind(YaccKind::Original(YaccOriginalActionKind::GenericParseTree))
            .process_file_in_src(file_path.to_str().unwrap())
        {
            Ok(_) => panic!("Expected error"),
            Err(e) => {
                let cs = e.downcast_ref::<CTConflictsError<u32>>();
                assert_eq!(cs.unwrap().stable.conflicts().unwrap().sr_len(), 1);
                assert_eq!(cs.unwrap().stable.conflicts().unwrap().rr_len(), 1);
            }
        }
    }
}
