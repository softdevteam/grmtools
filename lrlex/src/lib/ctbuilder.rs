//! Build grammars at run-time.

use std::{
    any::type_name,
    collections::{HashMap, HashSet},
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
use proc_macro2::TokenStream;
use quote::{format_ident, quote, ToTokens, TokenStreamExt};
use regex::Regex;
use serde::Serialize;

use crate::{DefaultLexerTypes, LRNonStreamingLexerDef, LexFlags, LexerDef, UNSPECIFIED_LEX_FLAGS};

const RUST_FILE_EXT: &str = "rs";

lazy_static! {
    static ref RE_TOKEN_ID: Regex = Regex::new(r"^[a-zA-Z_][a-zA-Z_0-9]*$").unwrap();
    static ref GENERATED_PATHS: Mutex<HashSet<PathBuf>> = Mutex::new(HashSet::new());
}

#[non_exhaustive]
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

impl ToTokens for Visibility {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        tokens.extend(match self {
            Visibility::Private => quote!(),
            Visibility::Public => quote! {pub},
            Visibility::PublicSuper => quote! {pub(super)},
            Visibility::PublicSelf => quote! {pub(self)},
            Visibility::PublicCrate => quote! {pub(crate)},
            Visibility::PublicIn(data) => {
                let other = str::parse::<TokenStream>(data).unwrap();
                quote! {pub(in #other)}
            }
        })
    }
}

/// Specifies the [Rust Edition] that will be emitted during code generation.
///
/// [Rust Edition]: https://doc.rust-lang.org/edition-guide/rust-2021/index.html
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[non_exhaustive]
pub enum RustEdition {
    Rust2015,
    Rust2018,
    Rust2021,
}

/// The quote impl of `ToTokens` for `Option` prints an empty string for `None`
/// and the inner value for `Some(inner_value)`.
///
/// This wrapper instead emits both `Some` and `None` variants.
/// See: [quote #20](https://github.com/dtolnay/quote/issues/20)
struct QuoteOption<T>(Option<T>);

impl<T: ToTokens> ToTokens for QuoteOption<T> {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        tokens.append_all(match self.0 {
            Some(ref t) => quote! { ::std::option::Option::Some(#t) },
            None => quote! { ::std::option::Option::None },
        });
    }
}

/// This wrapper adds a missing impl of `ToTokens` for tuples.
/// For a tuple `(a, b)` emits `(a.to_tokens(), b.to_tokens())`
struct QuoteTuple<T>(T);

impl<A: ToTokens, B: ToTokens> ToTokens for QuoteTuple<(A, B)> {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let (a, b) = &self.0;
        tokens.append_all(quote!((#a, #b)));
    }
}

/// The wrapped `&str` value will be emitted with a call to `to_string()`
struct QuoteToString<'a>(&'a str);

impl ToTokens for QuoteToString<'_> {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let x = &self.0;
        tokens.append_all(quote! { #x.to_string() });
    }
}

/// A `CTLexerBuilder` allows one to specify the criteria for building a statically generated
/// lexer.
pub struct CTLexerBuilder<'a, LexerTypesT: LexerTypes = DefaultLexerTypes<u32>>
where
    LexerTypesT::StorageT: Debug + Eq + Hash + ToTokens,
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
    force_lex_flags: LexFlags,
    default_lex_flags: LexFlags,
}

impl CTLexerBuilder<'_, DefaultLexerTypes<u32>> {
    /// Create a new [CTLexerBuilder].
    pub fn new() -> Self {
        CTLexerBuilder::<DefaultLexerTypes<u32>>::new_with_lexemet()
    }
}

impl<'a, LexerTypesT: LexerTypes> CTLexerBuilder<'a, LexerTypesT>
where
    LexerTypesT::StorageT:
        'static + Debug + Eq + Hash + PrimInt + Serialize + TryFrom<usize> + Unsigned + ToTokens,
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
            force_lex_flags: UNSPECIFIED_LEX_FLAGS,
            default_lex_flags: UNSPECIFIED_LEX_FLAGS,
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
        if std::env::var("OUT_DIR").is_ok() {
            println!("cargo:rerun-if-changed={}", lexerp.display());
        }
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

        let lex_src = read_to_string(lexerp)
            .map_err(|e| format!("When reading '{}': {e}", lexerp.display()))?;
        let line_cache = NewlineCache::from_str(&lex_src).unwrap();
        let (mut lexerdef, lex_flags): (Box<dyn LexerDef<LexerTypesT>>, LexFlags) = match self
            .lexerkind
        {
            LexerKind::LRNonStreamingLexer => {
                let lexerdef = LRNonStreamingLexerDef::<LexerTypesT>::new_with_options(
                    &lex_src,
                    self.force_lex_flags.clone(),
                    self.default_lex_flags.clone(),
                )
                .map_err(|errs| {
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
                })?;
                let lex_flags = lexerdef.lex_flags().cloned();
                (Box::new(lexerdef), lex_flags.unwrap())
            }
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

        let mut has_unallowed_missing = false;
        if !self.allow_missing_terms_in_lexer {
            if let Some(ref mfl) = missing_from_lexer {
                eprintln!("Error: the following tokens are used in the grammar but are not defined in the lexer:");
                for n in mfl {
                    eprintln!("    {}", n);
                }
                has_unallowed_missing = true;
            }
        }
        if !self.allow_missing_tokens_in_parser {
            if let Some(ref mfp) = missing_from_parser {
                eprintln!("Error: the following tokens are defined in the lexer but not used in the grammar:");
                for n in mfp {
                    eprintln!("    {}", n);
                }
                has_unallowed_missing = true;
            }
        }
        if has_unallowed_missing {
            fs::remove_file(outp).ok();
            panic!();
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
        let mod_name = format_ident!("{}", mod_name);
        let mut lexerdef_func_impl = {
            let LexFlags {
                allow_wholeline_comments,
                dot_matches_new_line,
                multi_line,
                octal,
                posix_escapes,
                case_insensitive,
                unicode,
                swap_greed,
                ignore_whitespace,
                size_limit,
                dfa_size_limit,
                nest_limit,
            } = lex_flags;
            let allow_wholeline_comments = QuoteOption(allow_wholeline_comments);
            let dot_matches_new_line = QuoteOption(dot_matches_new_line);
            let multi_line = QuoteOption(multi_line);
            let octal = QuoteOption(octal);
            let posix_escapes = QuoteOption(posix_escapes);
            let case_insensitive = QuoteOption(case_insensitive);
            let unicode = QuoteOption(unicode);
            let swap_greed = QuoteOption(swap_greed);
            let ignore_whitespace = QuoteOption(ignore_whitespace);
            let size_limit = QuoteOption(size_limit);
            let dfa_size_limit = QuoteOption(dfa_size_limit);
            let nest_limit = QuoteOption(nest_limit);

            // Code gen for the lexerdef() `lex_flags` variable.
            quote! {
                let mut lex_flags = ::lrlex::DEFAULT_LEX_FLAGS;
                lex_flags.allow_wholeline_comments = #allow_wholeline_comments;
                lex_flags.dot_matches_new_line = #dot_matches_new_line;
                lex_flags.multi_line = #multi_line;
                lex_flags.octal = #octal;
                lex_flags.posix_escapes = #posix_escapes;
                lex_flags.case_insensitive = #case_insensitive;
                lex_flags.unicode = #unicode;
                lex_flags.swap_greed = #swap_greed;
                lex_flags.ignore_whitespace = #ignore_whitespace;
                lex_flags.size_limit = #size_limit;
                lex_flags.dfa_size_limit = #dfa_size_limit;
                lex_flags.nest_limit = #nest_limit;
                let lex_flags = lex_flags;
            }
        };
        {
            let start_states = lexerdef.iter_start_states();
            let rules = lexerdef.iter_rules().map(|r| {
                    let tok_id = QuoteOption(r.tok_id);
                    let n = QuoteOption(r.name().map(QuoteToString));
                    let target_state =
                        QuoteOption(r.target_state().map(|(x, y)| QuoteTuple((x, y))));
                    let n_span = r.name_span();
                    let regex = QuoteToString(&r.re_str);
                    let start_states = r.start_states();
                    // Code gen to construct a rule.
                    //
                    // We cannot `impl ToToken for Rule` because `Rule` never stores `lex_flags`,
                    // Thus we reference the local lex_flags variable bound earlier.
                    quote! {
                        Rule::new(::lrlex::unstable_api::InternalPublicApi, #tok_id, #n, #n_span, #regex.to_string(),
                                vec![#(#start_states),*], #target_state, &lex_flags).unwrap()
                    }
                });
            // Code gen for `lexerdef()`s rules and the stack of `start_states`.
            lexerdef_func_impl.append_all(quote! {
                let start_states: Vec<StartState> = vec![#(#start_states),*];
                let rules = vec![#(#rules),*];
            });
        }
        let lexerdef_ty = match self.lexerkind {
            LexerKind::LRNonStreamingLexer => {
                quote!(::lrlex::LRNonStreamingLexerDef)
            }
        };
        // Code gen for the lexerdef() return value referencing variables bound earlier.
        lexerdef_func_impl.append_all(quote! {
            #lexerdef_ty::from_rules(start_states, rules)
        });

        let mut token_consts = TokenStream::new();
        if let Some(rim) = self.rule_ids_map {
            for (name, id) in rim {
                if RE_TOKEN_ID.is_match(&name) {
                    let tok_ident = format_ident!("N_{}", name.to_ascii_uppercase());
                    let storaget =
                        str::parse::<TokenStream>(type_name::<LexerTypesT::StorageT>()).unwrap();
                    // Code gen for the constant token values.
                    let tok_const = quote! {
                        #[allow(dead_code)]
                        pub const #tok_ident: #storaget = #id;
                    };
                    token_consts.extend(tok_const)
                }
            }
        }
        let token_consts = token_consts.into_iter();
        let out_tokens = {
            let lexerdef_param = str::parse::<TokenStream>(type_name::<LexerTypesT>()).unwrap();
            let mod_vis = self.visibility;
            // Code gen for the generated module.
            quote! {
                #mod_vis mod #mod_name {
                    use ::lrlex::{LexerDef, Rule, StartState};
                    #[allow(dead_code)]
                    pub fn lexerdef() -> #lexerdef_ty<#lexerdef_param> {
                        #lexerdef_func_impl
                    }

                    #(#token_consts)*
                }
            }
        };

        // Pretty print it.
        let out_file = syn::parse_file(&out_tokens.to_string()).unwrap();
        let outs = prettyplease::unparse(&out_file);

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

    /// Enables `// comment` style parsing according to `flag``.
    /// When enabled comments can appear at the beginning of a line,
    /// and regular expressions with the `/` character should be escaped via `\/`.
    ///
    /// The default value is `false`.
    ///
    /// Setting this flag will override the same flag within a `%grmtools` section.
    pub fn allow_wholeline_comments(mut self, flag: bool) -> Self {
        self.force_lex_flags.allow_wholeline_comments = Some(flag);
        self
    }

    /// Sets the `regex::RegexBuilder` option of the same name.
    /// The default value is `true`.
    ///
    /// Setting this flag will override the same flag within a `%grmtools` section.
    pub fn dot_matches_new_line(mut self, flag: bool) -> Self {
        self.force_lex_flags.dot_matches_new_line = Some(flag);
        self
    }

    /// Sets the `regex::RegexBuilder` option of the same name.
    /// The default value is `true`.
    ///
    /// Setting this flag will override the same flag within a `%grmtools` section.
    pub fn multi_line(mut self, flag: bool) -> Self {
        self.force_lex_flags.multi_line = Some(flag);
        self
    }

    /// Enables posix lex compatible escape sequences according to `flag`.
    /// The default value is `false`.
    ///
    /// Setting this flag will override the same flag within a `%grmtools` section.
    pub fn posix_escapes(mut self, flag: bool) -> Self {
        self.force_lex_flags.posix_escapes = Some(flag);
        self
    }

    /// Sets the `regex::RegexBuilder` option of the same name.
    /// The default value is `true`.
    ///
    /// Setting this flag will override the same flag within a `%grmtools` section.
    pub fn octal(mut self, flag: bool) -> Self {
        self.force_lex_flags.octal = Some(flag);
        self
    }

    /// Sets the `regex::RegexBuilder` option of the same name.
    /// Default value is specified by regex.
    ///
    /// Setting this flag will override the same flag within a `%grmtools` section.
    pub fn swap_greed(mut self, flag: bool) -> Self {
        self.force_lex_flags.swap_greed = Some(flag);
        self
    }

    /// Sets the `regex::RegexBuilder` option of the same name.
    /// Default value is specified by regex.
    ///
    /// Setting this flag will override the same flag within a `%grmtools` section.
    pub fn ignore_whitespace(mut self, flag: bool) -> Self {
        self.force_lex_flags.ignore_whitespace = Some(flag);
        self
    }

    /// Sets the `regex::RegexBuilder` option of the same name.
    /// Default value is specified by regex.
    ///
    /// Setting this flag will override the same flag within a `%grmtools` section.
    pub fn unicode(mut self, flag: bool) -> Self {
        self.force_lex_flags.unicode = Some(flag);
        self
    }

    /// Sets the `regex::RegexBuilder` option of the same name.
    /// Default value is specified by regex.
    ///
    /// Setting this flag will override the same flag within a `%grmtools` section.
    pub fn case_insensitive(mut self, flag: bool) -> Self {
        self.force_lex_flags.case_insensitive = Some(flag);
        self
    }

    /// Sets the `regex::RegexBuilder` option of the same name.
    /// Default value is specified by regex.
    ///
    /// Setting this flag will override the same flag within a `%grmtools` section.
    pub fn size_limit(mut self, sz: usize) -> Self {
        self.force_lex_flags.size_limit = Some(sz);
        self
    }

    /// Sets the `regex::RegexBuilder` option of the same name.
    /// Default value is specified by regex.
    ///
    /// Setting this flag will override the same flag within a `%grmtools` section.
    pub fn dfa_size_limit(mut self, sz: usize) -> Self {
        self.force_lex_flags.dfa_size_limit = Some(sz);
        self
    }

    /// Sets the `regex::RegexBuilder` option of the same name.
    /// Default value is specified by regex.
    ///
    /// Setting this flag will override the same flag within a `%grmtools` section.
    pub fn nest_limit(mut self, lim: u32) -> Self {
        self.force_lex_flags.nest_limit = Some(lim);
        self
    }

    /// `Some` values in the specified `flags` will be used as a default value
    /// unless the specified value has already been specified previously via `CTLexerBuilder`
    /// or was specified in the `%grmtools` section of a *.l* file.
    pub fn default_lex_flags(mut self, flags: LexFlags) -> Self {
        self.default_lex_flags = flags;
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
