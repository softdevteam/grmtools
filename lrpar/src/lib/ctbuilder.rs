//! Build grammars at compile-time so that they can be statically included into a binary.

use std::{
    collections::HashMap,
    convert::AsRef,
    env::{current_dir, var},
    error::Error,
    fmt::{self, Debug},
    fs::{self, create_dir_all, read_to_string, File},
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

const ACTION_PREFIX: &str = "__gt_";
const GLOBAL_PREFIX: &str = "__GT_";
const ACTIONS_KIND: &str = "__GTActionsKind";
const ACTIONS_KIND_PREFIX: &str = "AK";
const ACTIONS_KIND_HIDDEN: &str = "__GTActionsKindHidden";

const GRM_FILE_EXT: &str = "grm";
const RUST_FILE_EXT: &str = "rs";
const SGRAPH_FILE_EXT: &str = "sgraph";
const STABLE_FILE_EXT: &str = "stable";

lazy_static! {
    static ref RE_DOL_NUM: Regex = Regex::new(r"\$([0-9]+)").unwrap();
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
pub struct CTParserBuilder<'a, StorageT = u32>
where
    StorageT: Eq + Hash
{
    // Anything stored in here (except `conflicts` and `error_on_conflict`) almost certainly needs
    // to be included as part of the rebuild_cache function below so that, if it's changed, the
    // grammar is rebuilt.
    mod_name: Option<&'a str>,
    recoverer: RecoveryKind,
    yacckind: Option<YaccKind>,
    error_on_conflicts: bool,
    conflicts: Option<(
        YaccGrammar<StorageT>,
        StateGraph<StorageT>,
        StateTable<StorageT>
    )>,
    phantom: PhantomData<StorageT>
}

impl<'a> CTParserBuilder<'a, u32> {
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

impl<'a, StorageT> CTParserBuilder<'a, StorageT>
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
            mod_name: None,
            recoverer: RecoveryKind::MF,
            yacckind: None,
            error_on_conflicts: true,
            conflicts: None,
            phantom: PhantomData
        }
    }

    /// Set the generated module name to `mod_name`. If no module name is specified,
    /// [`process_file`](#method.process_file) will attempt to create a sensible default based on
    /// the input filename.
    pub fn mod_name(mut self, mod_name: &'a str) -> Self {
        self.mod_name = Some(mod_name);
        self
    }

    /// Set the recoverer for this parser to `rk`.
    pub fn recoverer(mut self, rk: RecoveryKind) -> Self {
        self.recoverer = rk;
        self
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

    /// Given the filename `a/b.y` as input, statically compile the grammar `src/a/b.y` into a Rust
    /// module which can then be imported using `lrpar_mod!("a/b.y")`. This is a convenience
    /// function around [`process_file`](#method.process_file) which makes it easier to compile
    /// grammar files stored in a project's `src/` directory: please see
    /// [`process_file`](#method.process_file) for additional constraints and information about the
    /// generated files.
    pub fn process_file_in_src(
        &mut self,
        srcp: &str
    ) -> Result<HashMap<String, StorageT>, Box<dyn Error>> {
        let mut inp = current_dir()?;
        inp.push("src");
        inp.push(srcp);
        let mut outp = PathBuf::new();
        outp.push(var("OUT_DIR").unwrap());
        outp.push(Path::new(srcp).parent().unwrap().to_str().unwrap());
        create_dir_all(&outp)?;
        let mut leaf = Path::new(srcp)
            .file_name()
            .unwrap()
            .to_str()
            .unwrap()
            .to_owned();
        leaf.push_str(&format!(".{}", RUST_FILE_EXT));
        outp.push(leaf);
        self.process_file(inp, outp)
    }

    /// Statically compile the Yacc file `inp` into Rust, placing the output into the file `outp`.
    /// Note that three additional files will be created with the same name as `outp` but with the
    /// extensions `grm`, `sgraph`, and `stable`, overwriting any existing files with those names.
    ///
    /// `outp` defines a module as follows:
    ///
    /// ```text
    ///   mod modname {
    ///     fn parse(lexemes: &::std::vec::Vec<::lrpar::Lexeme<StorageT>>) { ... }
    ///         -> (::std::option::Option<ActionT>,
    ///             ::std::vec::Vec<::lrpar::LexParseError<StorageT>>)> { ...}
    ///
    ///     fn token_epp<'a>(tidx: ::cfgrammar::TIdx<StorageT>) -> ::std::option::Option<&'a str> {
    ///       ...
    ///     }
    ///
    ///     ...
    ///   }
    /// ```
    ///
    /// where:
    ///  * `modname` is either:
    ///    * the module name specified [`mod_name`](#method.mod_name)
    ///    * or, if no module name was explicitly specified, then for the file `/a/b/c.y` the
    ///      module name is `c_y` (i.e. the file's leaf name, minus its extension, with a prefix of
    ///      `_y`).
    ///  * `ActionT` is either:
    ///    * the `%actiontype` value given to the grammar
    ///    * or, if the `yacckind` was set YaccKind::Original(YaccOriginalActionKind::UserAction),
    ///      it is [`Node<StorageT>`](../parser/enum.Node.html)
    ///
    /// # Panics
    ///
    /// If `StorageT` is not big enough to index the grammar's tokens, rules, or
    /// productions.
    pub fn process_file<P, Q>(
        &mut self,
        inp: P,
        outp: Q
    ) -> Result<HashMap<String, StorageT>, Box<dyn Error>>
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
        let mut outp_base = outp.as_ref().to_path_buf();
        outp_base.set_extension("");

        // We don't need to go through the full rigmarole of generating an output file if all of
        // the following are true: the output file exists; it is newer than the input file; and the
        // cache hasn't changed. The last of these might be surprising, but it's vital: we don't
        // know, for example, what the IDs map might be from one run to the next, and it might
        // change for reasons beyond lrpar's control. If it does change, that means that the lexer
        // and lrpar would get out of sync, so we have to play it safe and regenerate in such
        // cases.
        if let Ok(ref inmd) = fs::metadata(&inp) {
            if let Ok(ref out_rs_md) = fs::metadata(&outp) {
                if FileTime::from_last_modification_time(out_rs_md)
                    > FileTime::from_last_modification_time(inmd)
                {
                    if let Ok(outc) = read_to_string(&outp) {
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
        fs::remove_file(&outp).ok();

        let (sgraph, stable) = from_yacc(&grm, Minimiser::Pager)?;
        if stable.conflicts().is_some() && self.error_on_conflicts {
            return Err(Box::new(CTConflictsError {
                grm,
                sgraph,
                stable
            }));
        }

        let mod_name = match self.mod_name {
            Some(s) => s.to_owned(),
            None => {
                // The user hasn't specified a module name, so we create one automatically: what we
                // do is strip off all the filename extensions (note that it's likely that inp ends
                // with `y.rs`, so we potentially have to strip off more than one extension) and
                // then add `_y` to the end.
                let mut stem = inp.as_ref().to_str().unwrap();
                loop {
                    let new_stem = Path::new(stem).file_stem().unwrap().to_str().unwrap();
                    if stem == new_stem {
                        break;
                    }
                    stem = new_stem;
                }
                format!("{}_y", stem)
            }
        };
        self.output_file(
            &grm,
            &sgraph,
            &stable,
            &mod_name,
            outp_base,
            outp.as_ref().to_path_buf(),
            &cache
        )?;
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
    ) -> Result<(), Box<dyn Error>> {
        let mut outs = String::new();
        // Header
        outs.push_str(&format!("mod {} {{\n", mod_name));
        outs.push_str(
            "    #![allow(clippy::type_complexity)]
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
            "   Build time: {:?}\n",
            env!("VERGEN_BUILD_TIMESTAMP")
        ));

        cache.push_str(&format!("   Mod name: {:?}\n", self.mod_name));
        cache.push_str(&format!("   Recoverer: {:?}\n", self.recoverer));
        cache.push_str(&format!("   YaccKind: {:?}\n", self.yacckind));
        cache.push_str(&format!(
            "   Error on conflicts: {:?}\n",
            self.error_on_conflicts
        ));

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
    ) -> Result<String, Box<dyn Error>> {
        let mut outs = String::new();
        match self.yacckind.unwrap() {
            YaccKind::Original(YaccOriginalActionKind::UserAction) | YaccKind::Grmtools => {
                outs.push_str(&format!(
                    "
    #[allow(dead_code)]
    pub fn parse<'input>(lexer: &'input (dyn ::lrpar::Lexer<{storaget}> + 'input))
          -> (::std::option::Option<{actiont}>, ::std::vec::Vec<::lrpar::LexParseError<{storaget}>>)
    {{",
                    storaget = StorageT::type_name(),
                    actiont = grm.actiontype(self.user_start_ridx(grm)).as_ref().unwrap()
                ));
            }
            YaccKind::Original(YaccOriginalActionKind::GenericParseTree) => {
                outs.push_str(&format!(
                    "
    #[allow(dead_code)]
    pub fn parse(lexer: &dyn ::lrpar::Lexer<{storaget}>)
          -> (::std::option::Option<::lrpar::Node<{storaget}>>,
              ::std::vec::Vec<::lrpar::LexParseError<{storaget}>>)
    {{",
                    storaget = StorageT::type_name()
                ));
            }
            YaccKind::Original(YaccOriginalActionKind::NoAction) => {
                outs.push_str(&format!(
                    "
    #[allow(dead_code)]
    pub fn parse(lexer: &dyn ::lrpar::Lexer<{storaget}>)
          -> ::std::vec::Vec<::lrpar::LexParseError<{storaget}>>
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
        let (grm, sgraph, stable) = ::lrpar::ctbuilder::_reconstitute(include_bytes!(\"{}\"),
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
                    "\n        #[allow(clippy::type_complexity)]
        let mut actions: ::std::vec::Vec<&dyn Fn(::cfgrammar::RIdx<{storaget}>,
                       &'input (dyn ::lrpar::Lexer<{storaget}> + 'input),
                       ::lrpar::Span,
                       ::std::vec::Drain<::lrpar::parser::AStackType<{actionskind}<'input>, {storaget}>>)
                    -> {actionskind}<'input>> = ::std::vec::Vec::new();\n",
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
        match ::lrpar::RTParserBuilder::new(&grm, &sgraph, &stable)
            .recoverer(::lrpar::RecoveryKind::{recoverer})
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
        ::lrpar::RTParserBuilder::new(&grm, &sgraph, &stable)
            .recoverer(::lrpar::RecoveryKind::{})
            .parse_generictree(lexer)\n",
                    recoverer
                ));
            }
            YaccKind::Original(YaccOriginalActionKind::NoAction) => {
                outs.push_str(&format!(
                    "
        ::lrpar::RTParserBuilder::new(&grm, &sgraph, &stable)
            .recoverer(::lrpar::RecoveryKind::{})
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
            "    const {prefix}EPP: &[::std::option::Option<&str>] = &[{}];

    /// Return the %epp entry for token `tidx` (where `None` indicates \"the token has no
    /// pretty-printed value\"). Panics if `tidx` doesn't exist.
    #[allow(dead_code)]
    pub fn token_epp<'a>(tidx: ::cfgrammar::TIdx<{storaget}>) -> ::std::option::Option<&'a str> {{
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
                "    fn {prefix}wrapper_{}<'input>({prefix}ridx: ::cfgrammar::RIdx<{storaget}>,
                      {prefix}lexer: &'input (dyn ::lrpar::Lexer<{storaget}> + 'input),
                      {prefix}span: ::lrpar::Span,
                      mut {prefix}args: ::std::vec::Drain<::lrpar::parser::AStackType<{actionskind}<'input>, {storaget}>>)
                   -> {actionskind}<'input> {{",
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
            ::lrpar::parser::AStackType::ActionType({actionskind}::{actionskindprefix}{ref_ridx}(x)) => x,
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
            ::lrpar::parser::AStackType::Lexeme(l) => {{
                if l.inserted() {{
                    Err(l)
                }} else {{
                    Ok(l)
                }}
            }},
            ::lrpar::parser::AStackType::ActionType(_) => unreachable!()
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
                outs.push_str(&format!("\n        {actionskind}::{actionskindprefix}{ridx}({prefix}action_{pidx}({prefix}ridx, {prefix}lexer, {prefix}span, {args}))",
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
    enum {}<'input> {{\n",
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
        outs.push_str(&format!(
            "    _{actionskindhidden}(::std::marker::PhantomData<&'input ()>)
    }}\n\n",
            actionskindhidden = ACTIONS_KIND_HIDDEN
        ));

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
                        "::std::result::Result<::lrpar::Lexeme<{storaget}>, ::lrpar::Lexeme<{storaget}>>",
                        storaget = StorageT::type_name()
                    )
                };
                args.push(format!("mut {}arg_{}: {}", ACTION_PREFIX, i + 1, argt));
            }

            // Iterate over all $-arguments and replace them with their respective
            // element from the argument vector (e.g. $1 is replaced by args[0]). At
            // the same time extract &str from tokens and actiontype from nonterminals.
            outs.push_str(&format!(
                "    // {rulename}
    #[allow(clippy::too_many_arguments)]
    fn {prefix}action_{}<'input>({prefix}ridx: ::cfgrammar::RIdx<{storaget}>,
                     {prefix}lexer: &'input (dyn ::lrpar::Lexer<{storaget}> + 'input),
                     {prefix}span: ::lrpar::Span,
                     {args})
                  -> {actiont} {{\n",
                usize::from(pidx),
                rulename = grm.rule_name(grm.prod_to_rule(pidx)),
                storaget = StorageT::type_name(),
                prefix = ACTION_PREFIX,
                actiont = grm.actiontype(grm.prod_to_rule(pidx)).as_ref().unwrap(),
                args = args.join(",\n                     ")
            ));

            // Replace $1 ... $n with the correct local variable
            let pre_action = grm.action(pidx).as_ref().unwrap();
            let mut last = 0;
            loop {
                match pre_action[last..].find('$') {
                    Some(off) => {
                        if pre_action[last + off..].starts_with("$$") {
                            outs.push_str(&pre_action[last..last + off + "$".len()]);
                            last = last + off + "$$".len();
                        } else if pre_action[last + off..].starts_with("$lexer") {
                            outs.push_str(&pre_action[last..last + off]);
                            outs.push_str(
                                format!("{prefix}lexer", prefix = ACTION_PREFIX).as_str()
                            );
                            last = last + off + "$lexer".len();
                        } else if pre_action[last + off..].starts_with("$span") {
                            outs.push_str(&pre_action[last..last + off]);
                            outs.push_str(format!("{prefix}span", prefix = ACTION_PREFIX).as_str());
                            last = last + off + "$span".len();
                        } else if last + off + 1 < pre_action.len()
                            && pre_action[last + off + 1..].starts_with(|c: char| c.is_numeric())
                        {
                            outs.push_str(&pre_action[last..last + off]);
                            outs.push_str(format!("{prefix}arg_", prefix = ACTION_PREFIX).as_str());
                            last = last + off + "$".len();
                        } else {
                            panic!(
                                "Unknown text following '$' operator: {}",
                                &pre_action[last + off..]
                            );
                        }
                    }
                    None => {
                        outs.push_str(&pre_action[last..]);
                        break;
                    }
                }
            }

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
    ) -> Result<PathBuf, Box<dyn Error>> {
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
