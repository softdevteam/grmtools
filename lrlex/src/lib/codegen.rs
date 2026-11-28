use cfgrammar::{
    Span,
    header::{GrmtoolsSectionParser, Header, HeaderError, HeaderErrorKind, HeaderValue},
};
use lrpar::LexerTypes;

use crate::{
    DEFAULT_LEX_FLAGS, LRNonStreamingLexerDef, LexBuildError, LexFlags, LexerDef, LexerKind,
    Visibility,
};
use proc_macro2::{Ident, TokenStream};
use quote::{ToTokens, TokenStreamExt, format_ident, quote};
use regex::Regex;
use std::{
    any::type_name,
    collections::HashMap,
    fmt::{self, Write as _},
    marker::PhantomData,
    path::Path,
    sync::LazyLock,
};

static RE_TOKEN_ID: LazyLock<Regex> =
    LazyLock::new(|| Regex::new(r"^[a-zA-Z_][a-zA-Z_0-9]*$").unwrap());

#[non_exhaustive]
pub(crate) enum LexerSrcEnvError {
    GrmtoolsSectionError(Vec<HeaderError<Span>>),
    GrmtoolsSectionLookupError(HeaderError<Span>),
    MissingModName,
    LexBuildErrors(Vec<LexBuildError>),
}

impl From<Vec<HeaderError<Span>>> for LexerSrcEnvError {
    fn from(it: Vec<HeaderError<Span>>) -> Self {
        LexerSrcEnvError::GrmtoolsSectionError(it)
    }
}

impl From<HeaderError<Span>> for LexerSrcEnvError {
    fn from(it: HeaderError<Span>) -> Self {
        LexerSrcEnvError::GrmtoolsSectionLookupError(it)
    }
}

impl fmt::Display for LexerSrcEnvError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&match self {
            Self::GrmtoolsSectionError(errs) => errs
                .iter()
                .map(|e| e.to_string())
                .collect::<Vec<_>>()
                .join("\n"),
            Self::GrmtoolsSectionLookupError(e) => e.to_string(),
            Self::MissingModName => "Code generator requires a mod name".to_string(),
            Self::LexBuildErrors(_) => "Lex build error".to_string(),
        })
    }
}

pub(crate) struct LexerSrcEnv<'a, LexerTypesT>
where
    LexerTypesT: LexerTypes,
    usize: num_traits::AsPrimitive<LexerTypesT::StorageT>,
{
    src: &'a str,
    fallback_modname: Option<String>,
    phantom_storaget: PhantomData<LexerTypesT::StorageT>,
}

pub(crate) struct LexerBuildEnvArgs {
    mod_name: Option<String>,
    lexerkind: Option<LexerKind>,
    lex_flags: LexFlags,
    visibility: Visibility,
}

impl LexerBuildEnvArgs {
    pub(crate) fn new() -> Self {
        Self {
            mod_name: None,
            lexerkind: None,
            lex_flags: DEFAULT_LEX_FLAGS,
            visibility: Visibility::Private,
        }
    }

    pub(crate) fn mod_name(mut self, mod_name: Option<String>) -> Self {
        self.mod_name = mod_name;
        self
    }

    pub(crate) fn lexerkind(mut self, lexerkind: Option<LexerKind>) -> Self {
        self.lexerkind = lexerkind;
        self
    }

    pub(crate) fn visibility(mut self, visibility: Visibility) -> Self {
        self.visibility = visibility;
        self
    }

    pub(crate) fn lex_flags(mut self, lex_flags: LexFlags) -> Self {
        self.lex_flags = lex_flags;
        self
    }
}

pub(crate) struct LexerBuildEnv<LexerTypesT>
where
    LexerTypesT: LexerTypes,
    usize: num_traits::AsPrimitive<LexerTypesT::StorageT>,
{
    mod_name: String,
    lexerkind: LexerKind,
    lex_flags: LexFlags,
    visibility: Visibility,
    lexerdef: LRNonStreamingLexerDef<LexerTypesT>,
}

pub(crate) struct LexerCodegen<LexerTypesT>
where
    LexerTypesT: LexerTypes,
    usize: num_traits::AsPrimitive<LexerTypesT::StorageT>,
{
    rule_ids_map: Option<HashMap<String, LexerTypesT::StorageT>>,
    timestamp: String,
}

impl<'a, LexerTypesT> LexerSrcEnv<'a, LexerTypesT>
where
    LexerTypesT: LexerTypes,
    usize: num_traits::AsPrimitive<LexerTypesT::StorageT>,
{
    pub(crate) fn new(src: &'a str, path: Option<&Path>) -> LexerSrcEnv<'a, LexerTypesT> {
        let fallback_modname = if let Some(lexerp) = path {
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
            Some(format!("{}_l", stem))
        } else {
            None
        };
        LexerSrcEnv {
            src,
            fallback_modname,
            phantom_storaget: PhantomData,
        }
    }

    /// Looks up the `mod_name` from the `args`, and defaults to
    /// the `{filename}_l` with any file extenstion stripped off.
    fn resolve_mod_name(&self, args: &LexerBuildEnvArgs) -> Result<String, LexerSrcEnvError> {
        match &args.mod_name {
            Some(s) => Ok(s.to_owned()),
            None => self
                .fallback_modname
                .as_ref()
                .ok_or(LexerSrcEnvError::MissingModName)
                .map(|s| s.to_string()),
        }
    }

    fn parse_header(&self) -> Result<(Header<Span>, usize), Vec<HeaderError<Span>>> {
        GrmtoolsSectionParser::new(self.src, false).parse()
    }

    fn merge_lex_flags(
        &self,
        lex_flags: &mut LexFlags,
        header: &Header<Span>,
    ) -> Result<(), LexerSrcEnvError> {
        macro_rules! cvt_bool {
            ($key:literal,$field:ident,$errs:ident) => {
                if let Some(header_value) = header.get($key) {
                    if lex_flags.$field.is_some() {
                        $errs.push(HeaderError {
                            kind: HeaderErrorKind::ConflictingEntry("Already specified by builder"),
                            locations: vec![header_value.0],
                        });
                    } else {
                        match header_value.try_into() {
                            Ok(flag) => {
                                lex_flags.$field = Some(flag);
                            }
                            Err(e) => {
                                $errs.push(e);
                            }
                        }
                    }
                }
            };
        }

        macro_rules! cvt_num {
            ($key:literal,$field:ident,$typ:ty,$errs:ident) => {
                if let Some(header_value) = header.get($key) {
                    if lex_flags.$field.is_some() {
                        $errs.push(HeaderError {
                            kind: HeaderErrorKind::ConflictingEntry("Already specified by builder"),
                            locations: vec![header_value.0],
                        });
                    } else {
                        let val: Result<$typ, HeaderError<Span>> = header_value.try_into();
                        match val {
                            Ok(num) => {
                                lex_flags.$field = Some(num);
                            }
                            Err(e) => {
                                $errs.push(e);
                            }
                        }
                    }
                }
            };
        }

        let mut errs = Vec::new();
        cvt_bool!(
            "lrlex.allow_wholeline_comments",
            allow_wholeline_comments,
            errs
        );
        cvt_bool!("lrlex.posix_escapes", posix_escapes, errs);
        cvt_bool!("regex.dot_matches_new_line", dot_matches_new_line, errs);
        cvt_bool!("regex.multi_line", multi_line, errs);
        cvt_bool!("regex.swap_greed", swap_greed, errs);
        cvt_bool!("regex.ignore_whitespace", ignore_whitespace, errs);
        cvt_bool!("regex.unicode", unicode, errs);
        cvt_bool!("regex.case_insensitive", case_insensitive, errs);
        cvt_num!("regex.size_limit", size_limit, usize, errs);
        cvt_num!("regex.dfa_size_limit", dfa_size_limit, usize, errs);
        cvt_num!("regex.nest_limit", nest_limit, u32, errs);
        if errs.is_empty() {
            Ok(())
        } else {
            Err(LexerSrcEnvError::GrmtoolsSectionError(errs))
        }
    }

    pub(crate) fn build_env(
        self,
        mut args: LexerBuildEnvArgs,
    ) -> Result<LexerBuildEnv<LexerTypesT>, LexerSrcEnvError>
    where
        LexerTypesT: LexerTypes,
        usize: num_traits::AsPrimitive<LexerTypesT::StorageT>,
        LexerTypesT::StorageT: TryFrom<usize>,
    {
        let (header, _) = self.parse_header()?;
        self.merge_lex_flags(&mut args.lex_flags, &header)?;
        let mod_name = self.resolve_mod_name(&args)?;
        let lexerkind = match args.lexerkind {
            Some(lexerkind) => lexerkind,
            None => {
                if let Some(HeaderValue(_, lk_val)) = header.get("lrlex.lexerkind") {
                    LexerKind::try_from(lk_val)?
                } else {
                    LexerKind::LRNonStreamingLexer
                }
            }
        };
        let lex_flags = args.lex_flags;
        let (lexerdef, lex_flags): (LRNonStreamingLexerDef<LexerTypesT>, LexFlags) = match lexerkind
        {
            LexerKind::LRNonStreamingLexer => {
                let lexerdef =
                    LRNonStreamingLexerDef::<LexerTypesT>::new_with_options(self.src, lex_flags)
                        .map_err(LexerSrcEnvError::LexBuildErrors)?;

                let lex_flags = lexerdef.lex_flags().cloned();
                (lexerdef, lex_flags.unwrap())
            }
        };
        Ok(LexerBuildEnv {
            mod_name,
            lexerkind,
            visibility: args.visibility,
            lex_flags,
            lexerdef,
        })
    }
}

#[non_exhaustive]
pub(crate) enum LexerBuildEnvError {}

impl fmt::Display for LexerBuildEnvError {
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Ok(())
    }
}

impl<LexerTypesT> LexerBuildEnv<LexerTypesT>
where
    LexerTypesT: LexerTypes,
    usize: num_traits::AsPrimitive<LexerTypesT::StorageT>,
    LexerTypesT::StorageT: TryFrom<usize>,
{
    pub(crate) fn lexerkind(&self) -> &LexerKind {
        &self.lexerkind
    }

    pub(crate) fn mod_name(&self) -> &String {
        &self.mod_name
    }

    pub(crate) fn lexerdef(&self) -> &LRNonStreamingLexerDef<LexerTypesT> {
        &self.lexerdef
    }

    pub(crate) fn lexerdef_mut(&mut self) -> &mut LRNonStreamingLexerDef<LexerTypesT> {
        &mut self.lexerdef
    }

    pub(crate) fn lex_flags(&self) -> &LexFlags {
        &self.lex_flags
    }

    pub(crate) fn code_generator(
        &self,
        rule_ids_map: Option<HashMap<String, LexerTypesT::StorageT>>,
        timestamp: &str,
    ) -> Result<LexerCodegen<LexerTypesT>, LexerBuildEnvError> {
        Ok(LexerCodegen {
            rule_ids_map,
            timestamp: timestamp.to_string(),
        })
    }
}

#[non_exhaustive]
pub(crate) enum LexerCodegenError {
    InvalidRustIdentifierModName { mod_name: String, error: syn::Error },
}

impl fmt::Display for LexerCodegenError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&match self {
            Self::InvalidRustIdentifierModName { mod_name, error } => {
                format!("mod_name '{mod_name}' is not a valid rust identifier due to '{error}'")
            }
        })
    }
}

impl<LexerTypesT> LexerCodegen<LexerTypesT>
where
    LexerTypesT: LexerTypes,
    usize: num_traits::AsPrimitive<LexerTypesT::StorageT>,
    LexerTypesT::StorageT: TryFrom<usize> + ToTokens,
{
    pub(crate) fn rule_ids_map(&self) -> Option<&HashMap<String, LexerTypesT::StorageT>> {
        self.rule_ids_map.as_ref()
    }

    pub(crate) fn gen_mod_name(
        &self,
        build_env: &LexerBuildEnv<LexerTypesT>,
    ) -> Result<Ident, LexerCodegenError> {
        syn::parse_str::<proc_macro2::Ident>(build_env.mod_name()).map_err(|e| {
            LexerCodegenError::InvalidRustIdentifierModName {
                mod_name: build_env.mod_name().clone(),
                error: e,
            }
        })
    }

    pub(crate) fn gen_lex_flags_decl(&self, build_env: &LexerBuildEnv<LexerTypesT>) -> TokenStream {
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
        } = build_env.lex_flags();
        let allow_wholeline_comments = QuoteOption(allow_wholeline_comments.as_ref());
        let dot_matches_new_line = QuoteOption(dot_matches_new_line.as_ref());
        let multi_line = QuoteOption(multi_line.as_ref());
        let octal = QuoteOption(octal.as_ref());
        let posix_escapes = QuoteOption(posix_escapes.as_ref());
        let case_insensitive = QuoteOption(case_insensitive.as_ref());
        let unicode = QuoteOption(unicode.as_ref());
        let swap_greed = QuoteOption(swap_greed.as_ref());
        let ignore_whitespace = QuoteOption(ignore_whitespace.as_ref());
        let size_limit = QuoteOption(size_limit.as_ref());
        let dfa_size_limit = QuoteOption(dfa_size_limit.as_ref());
        let nest_limit = QuoteOption(nest_limit.as_ref());

        // Code gen for the lexerdef() `lex_flags` variable.
        quote! {
            let mut lex_flags = ::lrlex::DEFAULT_LEX_FLAGS;
            lex_flags.allow_wholeline_comments = #allow_wholeline_comments.or(::lrlex::DEFAULT_LEX_FLAGS.allow_wholeline_comments);
            lex_flags.dot_matches_new_line = #dot_matches_new_line.or(::lrlex::DEFAULT_LEX_FLAGS.dot_matches_new_line);
            lex_flags.multi_line = #multi_line.or(::lrlex::DEFAULT_LEX_FLAGS.multi_line);
            lex_flags.octal = #octal.or(::lrlex::DEFAULT_LEX_FLAGS.octal);
            lex_flags.posix_escapes = #posix_escapes.or(::lrlex::DEFAULT_LEX_FLAGS.posix_escapes);
            lex_flags.case_insensitive = #case_insensitive.or(::lrlex::DEFAULT_LEX_FLAGS.case_insensitive);
            lex_flags.unicode = #unicode.or(::lrlex::DEFAULT_LEX_FLAGS.unicode);
            lex_flags.swap_greed = #swap_greed.or(::lrlex::DEFAULT_LEX_FLAGS.swap_greed);
            lex_flags.ignore_whitespace = #ignore_whitespace.or(::lrlex::DEFAULT_LEX_FLAGS.ignore_whitespace);
            lex_flags.size_limit = #size_limit.or(::lrlex::DEFAULT_LEX_FLAGS.size_limit);
            lex_flags.dfa_size_limit = #dfa_size_limit.or(::lrlex::DEFAULT_LEX_FLAGS.dfa_size_limit);
            lex_flags.nest_limit = #nest_limit.or(::lrlex::DEFAULT_LEX_FLAGS.nest_limit);
            let lex_flags = lex_flags;
        }
    }

    pub(crate) fn gen_rules_val(&self, build_env: &LexerBuildEnv<LexerTypesT>) -> TokenStream {
        let rules = build_env.lexerdef.iter_rules().map(|r| {
            let tok_id = QuoteOption(r.tok_id);
            let n = QuoteOption(r.name().map(QuoteToString));
            let target_state = QuoteOption(r.target_state().map(|(x, y)| QuoteTuple((x, y))));
            let n_span = r.name_span();
            let regex = QuoteToString(&r.re_str);
            let start_states = r.start_states();
            // Code gen to construct a rule.
            //
            // We cannot `impl ToToken for Rule` because `Rule` never stores `lex_flags`,
            // Thus we reference the local lex_flags variable bound earlier.
            quote! {
                Rule::new(::lrlex::unstable_api::InternalPublicApi, #tok_id, #n, #n_span, #regex,
                        vec![#(#start_states),*], #target_state, &lex_flags).unwrap()
            }
        });
        // Code gen for `lexerdef()`s rules and the stack of `start_states`.
        quote! {
            let rules = vec![#(#rules),*];
        }
    }

    pub(crate) fn gen_start_states_val(
        &self,
        build_env: &LexerBuildEnv<LexerTypesT>,
    ) -> TokenStream {
        let start_states = build_env.lexerdef.iter_start_states();
        quote! {
            let start_states: Vec<StartState> = vec![#(#start_states),*];
        }
    }

    pub(crate) fn gen_lexerdef_ty(&self, build_env: &LexerBuildEnv<LexerTypesT>) -> TokenStream {
        match build_env.lexerkind() {
            LexerKind::LRNonStreamingLexer => {
                quote!(::lrlex::LRNonStreamingLexerDef)
            }
        }
    }

    pub(crate) fn gen_instantiate_lexerdef(
        &self,
        build_env: &LexerBuildEnv<LexerTypesT>,
    ) -> TokenStream {
        let lexerdef_ty = self.gen_lexerdef_ty(build_env);
        quote! {
            #lexerdef_ty::from_rules(start_states, rules)
        }
    }

    pub(crate) fn gen_token_consts(&self) -> TokenStream {
        let mut token_consts = TokenStream::new();
        if let Some(rim) = self.rule_ids_map() {
            let mut rim_sorted = Vec::from_iter(rim.iter());
            rim_sorted.sort_by_key(|(k, _)| *k);
            for (name, id) in rim_sorted {
                if RE_TOKEN_ID.is_match(name) {
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
        token_consts
    }

    pub(crate) fn generate_lex_module(
        &self,
        build_env: &LexerBuildEnv<LexerTypesT>,
    ) -> Result<TokenStream, LexerCodegenError> {
        let mod_name = self.gen_mod_name(build_env)?;
        let mut lexerdef_func_impl = self.gen_lex_flags_decl(build_env);
        lexerdef_func_impl.append_all(self.gen_start_states_val(build_env));
        lexerdef_func_impl.append_all(self.gen_rules_val(build_env));
        // Code gen for the lexerdef() return value referencing variables bound earlier.
        lexerdef_func_impl.append_all(self.gen_instantiate_lexerdef(build_env));
        let lexerdef_ty = self.gen_lexerdef_ty(build_env);
        let token_consts = self.gen_token_consts();
        let token_consts = token_consts.into_iter();
        let lexerdef_param = str::parse::<TokenStream>(type_name::<LexerTypesT>()).unwrap();
        let mod_vis = &build_env.visibility;
        // Code gen for the generated module.
        Ok(quote! {
            #mod_vis mod #mod_name {
                use ::lrlex::{LexerDef, Rule, StartState};
                #[allow(dead_code)]
                pub fn lexerdef() -> #lexerdef_ty<#lexerdef_param> {
                    #lexerdef_func_impl
                }

                #(#token_consts)*
            }
        })
    }

    pub(crate) fn generate(
        &self,
        build_env: &LexerBuildEnv<LexerTypesT>,
    ) -> Result<String, LexerCodegenError> {
        // Try and run a code formatter on the generated code.
        let unformatted = self.generate_lex_module(build_env)?.to_string();
        let mut outs = String::new();
        // Record the time that this version of lrlex was built. If the source code changes and rustc
        // forces a recompile, this will change this value, causing anything which depends on this
        // build of lrlex to be recompiled too.
        let timestamp = &self.timestamp;
        write!(outs, "// lrlex build time: {}\n\n", quote!(#timestamp),).ok();
        outs.push_str(
            &syn::parse_str(&unformatted)
                .map(|syntax_tree| prettyplease::unparse(&syntax_tree))
                .unwrap_or(unformatted),
        );
        Ok(outs)
    }
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

/// The wrapped `&str` value will be emitted with a call to `to_string()`
struct QuoteToString<'a>(&'a str);

impl ToTokens for QuoteToString<'_> {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let x = &self.0;
        tokens.append_all(quote! { #x.to_string() });
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
