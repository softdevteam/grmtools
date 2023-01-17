//! Build grammars at run-time.

use std::{
    any::type_name,
    borrow::Cow,
    collections::{HashMap, HashSet},
    convert::AsRef,
    env::{current_dir, var},
    error::Error,
    fmt::{Debug, Display, Write as _},
    fs::{self, create_dir_all, read_to_string, File},
    hash::Hash,
    io::Write,
    path::{Path, PathBuf},
    str::FromStr,
    sync::Mutex,
};

use cfgrammar::{newlinecache::NewlineCache, Spanned};
use lazy_static::lazy_static;
use lrpar::{CTParserBuilder, LexerTypes};
use num_traits::{AsPrimitive, PrimInt, Unsigned};
use quote::quote;
use regex::Regex;
use serde::Serialize;

use crate::{DefaultLexerTypes, LRNonStreamingLexerDef, LexerDef};

const RUST_FILE_EXT: &str = "rs";

lazy_static! {
    static ref RE_TOKEN_ID: Regex = Regex::new(r"^[a-zA-Z_][a-zA-Z_0-9]*$").unwrap();
    static ref GENERATED_PATHS: Mutex<HashSet<PathBuf>> = Mutex::new(HashSet::new());
}

pub enum LexerKind {
    LRNonStreamingLexer,
}

/// Specify the visibility of the module generated by [CTLexerBuilder].
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Visibility {
    /// Module-level visibility only.
    Private,
    /// `pub`
    Public,
    /// `pub(super)`
    PublicSuper,
    /// `pub(self)`
    PublicSelf,
    /// `pub(crate)`
    PublicCrate,
    /// `pub(in {arg})`
    PublicIn(String),
}

impl Visibility {
    fn cow_str(&self) -> Cow<'static, str> {
        match self {
            Visibility::Private => Cow::from(""),
            Visibility::Public => Cow::from("pub"),
            Visibility::PublicSuper => Cow::from("pub(super)"),
            Visibility::PublicSelf => Cow::from("pub(self)"),
            Visibility::PublicCrate => Cow::from("pub(crate)"),
            Visibility::PublicIn(data) => Cow::from(format!("pub(in {})", data)),
        }
    }
}

/// Specifies the [Rust Edition] that will be emitted during code generation.
///
/// [Rust Edition]: https://doc.rust-lang.org/edition-guide/rust-2021/index.html
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum RustEdition {
    Rust2015,
    Rust2018,
    Rust2021,
}

/// A `CTLexerBuilder` allows one to specify the criteria for building a statically generated
/// lexer.
pub struct CTLexerBuilder<'a, LexerTypesT: LexerTypes = DefaultLexerTypes<u32>>
where
    LexerTypesT::StorageT: Debug + Eq + Hash,
    usize: num_traits::AsPrimitive<LexerTypesT::StorageT>,
{
    lrpar_config: Option<Box<dyn Fn(CTParserBuilder<LexerTypesT>) -> CTParserBuilder<LexerTypesT>>>,
    lexer_path: Option<PathBuf>,
    output_path: Option<PathBuf>,
    lexerkind: LexerKind,
    mod_name: Option<&'a str>,
    visibility: Visibility,
    rust_edition: RustEdition,
    rule_ids_map: Option<HashMap<String, LexerTypesT::StorageT>>,
    allow_missing_terms_in_lexer: bool,
    allow_missing_tokens_in_parser: bool,
}

impl<'a> CTLexerBuilder<'a, DefaultLexerTypes<u32>> {
    /// Create a new [CTLexerBuilder].
    pub fn new() -> Self {
        CTLexerBuilder::<DefaultLexerTypes<u32>>::new_with_lexemet()
    }
}

impl<'a, LexerTypesT: LexerTypes> CTLexerBuilder<'a, LexerTypesT>
where
    LexerTypesT::StorageT:
        'static + Debug + Eq + Hash + PrimInt + Serialize + TryFrom<usize> + Unsigned,
    usize: AsPrimitive<LexerTypesT::StorageT>,
{
    /// Create a new [CTLexerBuilder].
    ///
    /// `LexerTypesT::StorageT` must be an unsigned integer type (e.g. `u8`, `u16`) which is big enough
    /// to index all the tokens, rules, and productions in the lexer and less than or equal in size
    /// to `usize` (e.g. on a 64-bit machine `u128` would be too big). If you are lexing large
    /// files, the additional storage requirements of larger integer types can be noticeable, and
    /// in such cases it can be worth specifying a smaller type. `StorageT` defaults to `u32` if
    /// unspecified.
    ///
    /// # Examples
    ///
    /// ```text
    /// CTLexerBuilder::<DefaultLexerTypes<u8>>::new_with_lexemet()
    ///     .lexer_in_src_dir("grm.l", None)?
    ///     .build()?;
    /// ```
    pub fn new_with_lexemet() -> Self {
        CTLexerBuilder {
            lrpar_config: None,
            lexer_path: None,
            output_path: None,
            lexerkind: LexerKind::LRNonStreamingLexer,
            mod_name: None,
            visibility: Visibility::Private,
            rust_edition: RustEdition::Rust2021,
            rule_ids_map: None,
            allow_missing_terms_in_lexer: false,
            allow_missing_tokens_in_parser: true,
        }
    }

    /// An optional convenience function to make it easier to create an (lrlex) lexer and (lrpar)
    /// parser in one shot. The closure passed to this function will be called during
    /// [CTLexerBuilder::build]: it will be passed an lrpar `CTParserBuilder` instance upon which
    /// it can set whatever lrpar options are desired. [`CTLexerBuilder`] will then create both the
    /// compiler and lexer and link them together as required.
    ///
    /// # Examples
    ///
    /// ```text
    /// CTLexerBuilder:::new()
    ///     .lrpar_config(|ctp| {
    ///         ctp.yacckind(YaccKind::Grmtools)
    ///             .grammar_in_src_dir("calc.y")
    ///             .unwrap()
    ///     })
    ///     .lexer_in_src_dir("calc.l")?
    ///     .build()?;
    /// ```
    pub fn lrpar_config<F>(mut self, config_func: F) -> Self
    where
        F: 'static + Fn(CTParserBuilder<LexerTypesT>) -> CTParserBuilder<LexerTypesT>,
    {
        self.lrpar_config = Some(Box::new(config_func));
        self
    }

    /// Set the input lexer path to a file relative to this project's `src` directory. This will
    /// also set the output path (i.e. you do not need to call [CTLexerBuilder::output_path]).
    ///
    /// For example if `a/b.l` is passed as `inp` then [CTLexerBuilder::build] will:
    ///   * use `src/a/b.l` as the input file.
    ///   * write output to a file which can then be imported by calling `lrlex_mod!("a/b.l")`.
    ///   * create a module in that output file named `b_l`.
    ///
    /// You can override the output path and/or module name by calling
    /// [CTLexerBuilder::output_path] and/or [CTLexerBuilder::mod_name], respectively, after
    /// calling this function.
    ///
    /// This is a convenience function that makes it easier to compile lexer files stored in a
    /// project's `src/` directory: please see [CTLexerBuilder::build] for additional constraints
    /// and information about the generated files. Note also that each `.l` file can only be
    /// processed once using this function: if you want to generate multiple lexers from a single
    /// `.l` file, you will need to use [CTLexerBuilder::output_path].
    pub fn lexer_in_src_dir<P>(mut self, srcp: P) -> Result<Self, Box<dyn Error>>
    where
        P: AsRef<Path>,
    {
        if !srcp.as_ref().is_relative() {
            return Err(format!(
                "Lexer path '{}' must be a relative path.",
                srcp.as_ref().to_str().unwrap_or("<invalid UTF-8>")
            )
            .into());
        }

        let mut lexp = current_dir()?;
        lexp.push("src");
        lexp.push(srcp.as_ref());
        self.lexer_path = Some(lexp);

        let mut outp = PathBuf::new();
        outp.push(var("OUT_DIR").unwrap());
        outp.push(srcp.as_ref().parent().unwrap().to_str().unwrap());
        create_dir_all(&outp)?;
        let mut leaf = srcp
            .as_ref()
            .file_name()
            .unwrap()
            .to_str()
            .unwrap()
            .to_owned();
        write!(leaf, ".{}", RUST_FILE_EXT).ok();
        outp.push(leaf);
        Ok(self.output_path(outp))
    }

    /// Set the input lexer path to `inp`. If specified, you must also call
    /// [CTLexerBuilder::output_path]. In general it is easier to use
    /// [CTLexerBuilder::lexer_in_src_dir].
    pub fn lexer_path<P>(mut self, inp: P) -> Self
    where
        P: AsRef<Path>,
    {
        self.lexer_path = Some(inp.as_ref().to_owned());
        self
    }

    /// Set the output lexer path to `outp`. Note that there are no requirements on `outp`: the
    /// file can exist anywhere you can create a valid [Path] to. However, if you wish to use
    /// [crate::lrlex_mod!] you will need to make sure that `outp` is in
    /// [std::env::var]`("OUT_DIR")` or one of its subdirectories.
    pub fn output_path<P>(mut self, outp: P) -> Self
    where
        P: AsRef<Path>,
    {
        self.output_path = Some(outp.as_ref().to_owned());
        self
    }

    /// Set the type of lexer to be generated to `lexerkind`.
    pub fn lexerkind(mut self, lexerkind: LexerKind) -> Self {
        self.lexerkind = lexerkind;
        self
    }

    /// Set the generated module name to `mod_name`. If no module name is specified,
    /// [`process_file`](#method.process_file) will attempt to create a sensible default based on
    /// the input filename.
    pub fn mod_name(mut self, mod_name: &'a str) -> Self {
        self.mod_name = Some(mod_name);
        self
    }

    /// Set the visibility of the generated module to `vis`. Defaults to `Visibility::Private`.
    pub fn visibility(mut self, vis: Visibility) -> Self {
        self.visibility = vis;
        self
    }

    /// Sets the rust edition to be used for generated code. Defaults to the latest edition of
    /// rust supported by grmtools.
    pub fn rust_edition(mut self, edition: RustEdition) -> Self {
        self.rust_edition = edition;
        self
    }

    /// Set this lexer builder's map of rule IDs to `rule_ids_map`. By default, lexing rules have
    /// arbitrary, but distinct, IDs. Setting the map of rule IDs (from rule names to `StorageT`)
    /// allows users to synchronise a lexer and parser and to check that all rules are used by both
    /// parts).
    pub fn rule_ids_map<T: std::borrow::Borrow<HashMap<String, LexerTypesT::StorageT>> + Clone>(
        mut self,
        rule_ids_map: T,
    ) -> Self {
        self.rule_ids_map = Some(rule_ids_map.borrow().to_owned());
        self
    }

    /// Statically compile the `.l` file specified by [CTLexerBuilder::lexer_path()] into Rust,
    /// placing the output into the file specified by [CTLexerBuilder::output_path()].
    ///
    /// The generated module follows the form:
    ///
    /// ```text
    ///    mod modname {
    ///      pub fn lexerdef() -> LexerDef<LexerTypesT> { ... }
    ///
    ///      ...
    ///    }
    /// ```
    ///
    /// where:
    ///  * `modname` is either:
    ///    * the module name specified by [CTLexerBuilder::mod_name()]
    ///    * or, if no module name was explicitly specified, then for the file `/a/b/c.l` the
    ///      module name is `c_l` (i.e. the file's leaf name, minus its extension, with a prefix of
    ///      `_l`).
    pub fn build(mut self) -> Result<CTLexer, Box<dyn Error>> {
        if let Some(ref lrcfg) = self.lrpar_config {
            let mut ctp = CTParserBuilder::<LexerTypesT>::new();
            ctp = lrcfg(ctp);
            let map = ctp.build()?;
            self.rule_ids_map = Some(map.token_map().to_owned());
        }

        let lexerp = self
            .lexer_path
            .as_ref()
            .expect("lexer_path must be specified before processing.");
        let outp = self
            .output_path
            .as_ref()
            .expect("output_path must be specified before processing.");

        {
            let mut lk = GENERATED_PATHS.lock().unwrap();
            if lk.contains(outp.as_path()) {
                return Err(format!("Generating two lexers to the same path ('{}') is not allowed: use CTLexerBuilder::output_path (and, optionally, CTLexerBuilder::mod_name) to differentiate them.", &outp.to_str().unwrap()).into());
            }
            lk.insert(outp.clone());
        }

        let lex_src = read_to_string(lexerp)?;
        let line_cache = NewlineCache::from_str(&lex_src).unwrap();
        let mut lexerdef: Box<dyn LexerDef<LexerTypesT>> = match self.lexerkind {
            LexerKind::LRNonStreamingLexer => Box::new(
                LRNonStreamingLexerDef::<LexerTypesT>::from_str(&lex_src).map_err(|errs| {
                    errs.iter()
                        .map(|e| {
                            if let Some((line, column)) = line_cache.byte_to_line_num_and_col_num(
                                &lex_src,
                                e.spans().first().unwrap().start(),
                            ) {
                                format!("{} at line {line} column {column}", e)
                            } else {
                                format!("{}", e)
                            }
                        })
                        .collect::<Vec<_>>()
                        .join("\n")
                })?,
            ),
        };
        let (missing_from_lexer, missing_from_parser) = match self.rule_ids_map {
            Some(ref rim) => {
                // Convert from HashMap<String, _> to HashMap<&str, _>
                let owned_map = rim
                    .iter()
                    .map(|(x, y)| (&**x, *y))
                    .collect::<HashMap<_, _>>();
                let (x, y) = lexerdef.set_rule_ids(&owned_map);
                (
                    x.map(|a| a.iter().map(|&b| b.to_string()).collect::<HashSet<_>>()),
                    y.map(|a| a.iter().map(|&b| b.to_string()).collect::<HashSet<_>>()),
                )
            }
            None => (None, None),
        };

        if !self.allow_missing_terms_in_lexer {
            if let Some(ref mfl) = missing_from_lexer {
                eprintln!("Error: the following tokens are used in the grammar but are not defined in the lexer:");
                for n in mfl {
                    eprintln!("    {}", n);
                }
                fs::remove_file(outp).ok();
                panic!();
            }
        }
        if !self.allow_missing_tokens_in_parser {
            if let Some(ref mfp) = missing_from_parser {
                eprintln!("Error: the following tokens are defined in the lexer but not used in the grammar:");
                for n in mfp {
                    eprintln!("    {}", n);
                }
                fs::remove_file(outp).ok();
                panic!();
            }
        }

        let mod_name = match self.mod_name {
            Some(s) => s.to_owned(),
            None => {
                // The user hasn't specified a module name, so we create one automatically: what we
                // do is strip off all the filename extensions (note that it's likely that inp ends
                // with `l.rs`, so we potentially have to strip off more than one extension) and
                // then add `_l` to the end.
                let mut stem = lexerp.to_str().unwrap();
                loop {
                    let new_stem = Path::new(stem).file_stem().unwrap().to_str().unwrap();
                    if stem == new_stem {
                        break;
                    }
                    stem = new_stem;
                }
                format!("{}_l", stem)
            }
        };

        let mut outs = String::new();
        //
        // Header

        let (lexerdef_name, lexerdef_type) = match self.lexerkind {
            LexerKind::LRNonStreamingLexer => (
                "LRNonStreamingLexerDef",
                format!(
                    "LRNonStreamingLexerDef<{lexertypest}>",
                    lexertypest = type_name::<LexerTypesT>()
                ),
            ),
        };

        write!(
            outs,
            "{mod_vis} mod {mod_name} {{
use lrlex::{{LexerDef, LRNonStreamingLexerDef, Rule, StartState}};

#[allow(dead_code)]
pub fn lexerdef() -> {lexerdef_type} {{
",
            mod_vis = self.visibility.cow_str(),
            mod_name = mod_name,
            lexerdef_type = lexerdef_type
        )
        .ok();

        outs.push_str("    let start_states: Vec<StartState> = vec![");
        for ss in lexerdef.iter_start_states() {
            let state_name = &ss.name;
            write!(
                outs,
                "
        StartState::new({}, {}, {}, ::cfgrammar::Span::new({}, {})),",
                ss.id,
                quote!(#state_name),
                ss.exclusive,
                ss.name_span.start(),
                ss.name_span.end()
            )
            .ok();
        }
        outs.push_str("\n    ];\n");
        outs.push_str("    let rules = vec![");

        // Individual rules
        for r in lexerdef.iter_rules() {
            let tok_id = match r.tok_id {
                Some(ref t) => format!("Some({:?})", t),
                None => "None".to_owned(),
            };
            let n = match r.name {
                Some(ref n) => format!("Some({}.to_string())", quote!(#n)),
                None => "None".to_owned(),
            };
            let target_state = match &r.target_state {
                Some((id, op)) => format!("Some(({}, ::lrlex::StartStateOperation::{:?}))", id, op),
                None => "None".to_owned(),
            };
            let n_span = format!(
                "::cfgrammar::Span::new({}, {})",
                r.name_span.start(),
                r.name_span.end()
            );
            let regex = &r.re_str;
            let start_states = r.start_states.as_slice();
            write!(
                outs,
                "
        Rule::new({}, {}, {}, {}.to_string(), {}.to_vec(), {}).unwrap(),",
                tok_id,
                n,
                n_span,
                quote!(#regex),
                quote!([#(#start_states),*]),
                target_state,
            )
            .ok();
        }

        // Footer
        write!(
            outs,
            "
    ];
    {lexerdef_name}::from_rules(start_states, rules)
}}

",
            lexerdef_name = lexerdef_name
        )
        .ok();

        // Token IDs
        if let Some(ref rim) = self.rule_ids_map {
            for (n, id) in rim {
                if RE_TOKEN_ID.is_match(n) {
                    write!(
                        outs,
                        "#[allow(dead_code)]\npub const T_{}: {} = {:?};\n",
                        n.to_ascii_uppercase(),
                        type_name::<LexerTypesT::StorageT>(),
                        *id
                    )
                    .ok();
                }
            }
        }

        // Footer
        outs.push('}');

        // If the file we're about to write out already exists with the same contents, then we
        // don't overwrite it (since that will force a recompile of the file, and relinking of the
        // binary etc).
        if let Ok(curs) = read_to_string(outp) {
            if curs == outs {
                return Ok(CTLexer {
                    missing_from_lexer,
                    missing_from_parser,
                });
            }
        }
        let mut f = File::create(outp)?;
        f.write_all(outs.as_bytes())?;
        Ok(CTLexer {
            missing_from_lexer,
            missing_from_parser,
        })
    }

    /// Given the filename `a/b.l` as input, statically compile the file `src/a/b.l` into a Rust
    /// module which can then be imported using `lrlex_mod!("a/b.l")`. This is a convenience
    /// function around [`process_file`](struct.CTLexerBuilder.html#method.process_file) which makes
    /// it easier to compile `.l` files stored in a project's `src/` directory: please see
    /// [`process_file`](#method.process_file) for additional constraints and information about the
    /// generated files.
    #[deprecated(
        since = "0.11.0",
        note = "Please use lexer_in_src_dir() and build() instead"
    )]
    #[allow(deprecated)]
    pub fn process_file_in_src(
        self,
        srcp: &str,
    ) -> Result<(Option<HashSet<String>>, Option<HashSet<String>>), Box<dyn Error>> {
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
        write!(leaf, ".{}", RUST_FILE_EXT).ok();
        outp.push(leaf);
        self.process_file(inp, outp)
    }

    /// Statically compile the `.l` file `inp` into Rust, placing the output into the file `outp`.
    /// The latter defines a module as follows:
    ///
    /// ```text
    ///    mod modname {
    ///      pub fn lexerdef() -> LexerDef<LexerTypesT::StorageT> { ... }
    ///
    ///      ...
    ///    }
    /// ```
    ///
    /// where:
    ///  * `modname` is either:
    ///    * the module name specified [`mod_name`](#method.mod_name)
    ///    * or, if no module name was explicitly specified, then for the file `/a/b/c.l` the
    ///      module name is `c_l` (i.e. the file's leaf name, minus its extension, with a prefix of
    ///      `_l`).
    #[deprecated(
        since = "0.11.0",
        note = "Please use lexer_in_src_dir() and build() instead"
    )]
    pub fn process_file<P, Q>(
        mut self,
        inp: P,
        outp: Q,
    ) -> Result<(Option<HashSet<String>>, Option<HashSet<String>>), Box<dyn Error>>
    where
        P: AsRef<Path>,
        Q: AsRef<Path>,
    {
        self.lexer_path = Some(inp.as_ref().to_owned());
        self.output_path = Some(outp.as_ref().to_owned());
        let cl = self.build()?;
        Ok((
            cl.missing_from_lexer().map(|x| x.to_owned()),
            cl.missing_from_parser().map(|x| x.to_owned()),
        ))
    }

    /// If passed false, tokens used in the grammar but not defined in the lexer will cause a
    /// panic at lexer generation time. Defaults to false.
    pub fn allow_missing_terms_in_lexer(mut self, allow: bool) -> Self {
        self.allow_missing_terms_in_lexer = allow;
        self
    }

    /// If passed false, tokens defined in the lexer but not used in the grammar will cause a
    /// panic at lexer generation time. Defaults to true (since lexers sometimes define tokens such
    /// as reserved words, which are intentionally not in the grammar).
    pub fn allow_missing_tokens_in_parser(mut self, allow: bool) -> Self {
        self.allow_missing_tokens_in_parser = allow;
        self
    }
}

/// An interface to the result of [CTLexerBuilder::build()].
pub struct CTLexer {
    missing_from_lexer: Option<HashSet<String>>,
    missing_from_parser: Option<HashSet<String>>,
}

impl CTLexer {
    fn missing_from_lexer(&self) -> Option<&HashSet<String>> {
        self.missing_from_lexer.as_ref()
    }

    fn missing_from_parser(&self) -> Option<&HashSet<String>> {
        self.missing_from_parser.as_ref()
    }
}

/// Create a Rust module named `mod_name` that can be imported with
/// [`lrlex_mod!(mod_name)`](crate::lrlex_mod). The module contains one `const` `StorageT` per
/// token in `token_map`, with the token prefixed by `T_`. For example with `StorageT` `u8`,
/// `mod_name` `x`, and `token_map` `HashMap{"ID": 0, "INT": 1}` the generated module will look
/// roughly as follows:
///
/// ```rust,ignore
/// mod x {
///   pub const T_ID: u8 = 0;
///   pub const T_INT: u8 = 1;
/// }
/// ```
///
/// You can optionally remap names (for example, because the parser's token names do not lead to
/// valid Rust identifiers) by specifying the `rename_map` `HashMap`. For example, if `token_map`
/// is `HashMap{"+": 0, "ID": 1}` and `rename_map` is `HashMap{"+": "PLUS"}` then the generated
/// module will look roughly as follows:
///
/// ```rust,ignore
/// mod x {
///   pub const T_PLUS: u8 = 0;
///   pub const T_ID: u8 = 1;
/// }
/// ```
pub fn ct_token_map<StorageT: Display>(
    mod_name: &str,
    token_map: &HashMap<String, StorageT>,
    rename_map: Option<&HashMap<&str, &str>>,
) -> Result<(), Box<dyn Error>> {
    // Record the time that this version of lrlex was built. If the source code changes and rustc
    // forces a recompile, this will change this value, causing anything which depends on this
    // build of lrlex to be recompiled too.
    let mut outs = String::new();
    let timestamp = env!("VERGEN_BUILD_TIMESTAMP");
    write!(
        outs,
        "// lrlex build time: {}\n\nmod {} {{\n",
        quote!(#timestamp),
        mod_name
    )
    .ok();
    outs.push_str(
        &token_map
            .iter()
            .map(|(k, v)| {
                let k = match rename_map {
                    Some(rmap) => *rmap.get(k.as_str()).unwrap_or(&k.as_str()),
                    _ => k,
                };
                format!(
                    "    #[allow(dead_code)] pub const T_{}: {} = {};",
                    k,
                    type_name::<StorageT>(),
                    v
                )
            })
            .collect::<Vec<_>>()
            .join("\n"),
    );
    outs.push_str("\n}");

    let mut outp = PathBuf::from(var("OUT_DIR")?);
    outp.push(mod_name);
    outp.set_extension("rs");

    // If the file we're about to write out already exists with the same contents, then we
    // don't overwrite it (since that will force a recompile of the file, and relinking of the
    // binary etc).
    if let Ok(curs) = read_to_string(&outp) {
        if curs == outs {
            return Ok(());
        }
    }

    let mut f = File::create(outp)?;
    f.write_all(outs.as_bytes())?;
    Ok(())
}
