use crate::{LRNonStreamingLexerDef, LexFlags, LexerDef, Visibility, ctbuilder::LexerKind};
use cfgrammar::{
    header::{GrmtoolsSectionParser, Header, HeaderValue},
    span::{Location, Span},
};
use lrpar::{
    LexerTypes,
    diagnostics::{DiagnosticFormatter, SpannedDiagnosticFormatter},
};
use proc_macro2::{Ident, TokenStream};
use quote::{ToTokens, TokenStreamExt, format_ident, quote};
use regex::Regex;
use std::{
    any::type_name,
    borrow::Borrow,
    collections::HashMap,
    error::Error,
    fmt::{self, Display, Write as _},
    marker::PhantomData,
    path::Path,
    sync::LazyLock,
};

static RE_TOKEN_ID: LazyLock<Regex> =
    LazyLock::new(|| Regex::new(r"^[a-zA-Z_][a-zA-Z_0-9]*$").unwrap());

use crate::ctbuilder::ERROR;
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

/// Currently this is kind of a hodge podge of everything between parsing/validation
/// and code generation, from lex source input strings, to rust source output strings.
///
/// This probably needs a better name, as note that the self variable only gets used
/// for the former parsering/validation stages, and the latter codegen phases are all
/// implemented through associated functions.
pub(crate) struct LexSrcEnv<'a> {
    src: &'a str,
    // We store the path here so we can generate a module name from it if needed.
    // But should never use it for filesystem interaction within this module.
    path: &'a Path,
    diagnostics: SpannedDiagnosticFormatter<'a>,
    header: Header<Location>,
}

pub(crate) struct LexCodegenArgs<'a> {
    lexerkind: Option<LexerKind>,
    mod_name: Option<&'a str>,
    visibility: Visibility,
}

pub(crate) struct LexCodegen<LexerTypesT>
where
    LexerTypesT: LexerTypes,
    usize: num_traits::AsPrimitive<LexerTypesT::StorageT>,
{
    kind: LexerKind,
    lexerdef: LRNonStreamingLexerDef<LexerTypesT>,
    lex_flags: LexFlags,
    mod_name: Ident,
    rule_ids_map: Option<HashMap<String, LexerTypesT::StorageT>>,
    visibility: Visibility,
}

impl<'a> LexCodegenArgs<'a> {
    pub(crate) fn new() -> LexCodegenArgs<'a> {
        LexCodegenArgs {
            lexerkind: None,
            mod_name: None,
            visibility: Visibility::Private,
        }
    }

    pub(crate) fn lexerkind(mut self, lexerkind: Option<LexerKind>) -> Self {
        self.lexerkind = lexerkind;
        self
    }
    pub(crate) fn mod_name(mut self, mod_name: Option<&'a str>) -> Self {
        self.mod_name = mod_name;
        self
    }
    pub(crate) fn visibility(mut self, visibility: Visibility) -> Self {
        self.visibility = visibility;
        self
    }
}

impl<'a> LexSrcEnv<'a> {

    pub(crate) fn new_with_defaults(src: &'a str, path: &'a Path, header: Header<Location>) -> LexSrcEnv<'a> {
        let diagnostics = SpannedDiagnosticFormatter::new(src, path);
        LexSrcEnv {
            src,
            path,
            header,
            diagnostics,
        }
    }

    pub(crate) fn lex_diag(&self) -> &SpannedDiagnosticFormatter<'a> {
        &self.diagnostics
    }

    fn merge_headers(&mut self) -> Result<(), Box<dyn Error>> {
        let (parsed_header, _) = self.parse_header()?;
        Ok(self.header.merge_from(parsed_header)?)
    }

    fn parse_header(&self) -> Result<(Header<Span>, usize), Box<dyn Error>> {
        GrmtoolsSectionParser::new(self.src, false)
            .parse()
            .map_err(|es| {
                let mut out = String::new();
                out.push_str(&format!(
                    "\n{ERROR}{}\n",
                    self.lex_diag()
                        .file_location_msg(" parsing the `%grmtools` section", None)
                ));
                for e in es {
                    out.push_str(&indent(
                        "     ",
                        &self.lex_diag().format_error(e).to_string(),
                    ));
                    out.push('\n');
                }
                ErrorString(out).into()
            })
    }

    fn extract_lexerkind(
        &mut self,
        lexerkind: Option<LexerKind>,
    ) -> Result<LexerKind, Box<dyn Error>> {
        self.header.mark_used(&"lexerkind".to_string());
        match lexerkind {
            Some(lexerkind) => Ok(lexerkind),
            None => {
                if let Some(HeaderValue(_, lk_val)) = self.header.get("lexerkind") {
                    Ok(LexerKind::try_from(lk_val)?)
                } else {
                    Ok(LexerKind::LRNonStreamingLexer)
                }
            }
        }
    }

    fn extract_lexerdef<LexerTypesT>(
        &mut self,
        lexerkind: &LexerKind,
    ) -> Result<(LRNonStreamingLexerDef<LexerTypesT>, LexFlags), Box<dyn Error>>
    where
        LexerTypesT: LexerTypes,
        LexerTypesT::StorageT: TryFrom<usize>,
        usize: num_traits::AsPrimitive<LexerTypesT::StorageT>,
    {
        let (lexerdef, lex_flags): (LRNonStreamingLexerDef<LexerTypesT>, LexFlags) = match lexerkind
        {
            LexerKind::LRNonStreamingLexer => {
                let lex_flags = LexFlags::try_from(&mut self.header)?;
                let lexerdef =
                    LRNonStreamingLexerDef::<LexerTypesT>::new_with_options(self.src, lex_flags)
                        .map_err(|errs| {
                            let mut out = String::new();
                            out.push_str(&format!(
                                "\n{ERROR}{}\n",
                                self.lex_diag().file_location_msg("", None)
                            ));
                            for e in errs {
                                out.push_str(&indent(
                                    "     ",
                                    &self.lex_diag().format_error(e).to_string(),
                                ));
                                out.push('\n');
                            }
                            ErrorString(out)
                        })?;
                let lex_flags = lexerdef.lex_flags().cloned();
                (lexerdef, lex_flags.unwrap())
            }
        };
        Ok((lexerdef, lex_flags))
    }

    fn check_unused_header_values(&self) -> Result<(), Box<dyn Error>> {
        let unused_header_values = self.header.unused();
        if !unused_header_values.is_empty() {
            Err(format!("Unused header values: {}", unused_header_values.join(", ")).into())
        } else {
            Ok(())
        }
    }

    fn mod_name_tokens(&self, mod_name: Option<&str>) -> Result<Ident, Box<dyn Error>> {
        let mod_name = match mod_name {
            Some(s) => s.to_owned(),
            None => {
                // The user hasn't specified a module name, so we create one automatically: what we
                // do is strip off all the filename extensions (note that it's likely that inp ends
                // with `l.rs`, so we potentially have to strip off more than one extension) and
                // then add `_l` to the end.
                let mut stem = self.path.to_str().unwrap();
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
        let mod_name =
            match syn::parse_str::<proc_macro2::Ident>(&mod_name) {
                Ok(s) => s,
                Err(e) => return Err(format!(
                    "CTLexerBuilder::mod_name(\"{}\") is not a valid rust identifier due to '{}'",
                    mod_name, e
                )
                .into()),
            };
        Ok(mod_name)
    }

    pub(crate) fn code_generator<'b, LexerTypesT>(
        &mut self,
        args: LexCodegenArgs<'b>,
    ) -> Result<LexCodegen<LexerTypesT>, Box<dyn Error>>
    where
        LexerTypesT: LexerTypes,
        LexerTypesT::StorageT: TryFrom<usize>,
        usize: num_traits::AsPrimitive<LexerTypesT::StorageT>,
    {
        self.merge_headers()?;
        let kind = self.extract_lexerkind(args.lexerkind)?;
        let (lexerdef, lex_flags) = self.extract_lexerdef::<LexerTypesT>(&kind)?;
        let mod_name = self.mod_name_tokens(args.mod_name)?;
        self.check_unused_header_values()?;
        let visibility = args.visibility;
        Ok(LexCodegen {
            kind,
            lexerdef,
            lex_flags,
            mod_name,
            rule_ids_map: None,
            visibility,
        })
    }
}

impl<LexerTypesT> LexCodegen<LexerTypesT>
where
    LexerTypesT: LexerTypes,
    usize: num_traits::AsPrimitive<LexerTypesT::StorageT>,
{
    #[cfg(test)]
    pub(crate) fn lexerkind(&self) -> &LexerKind {
        &self.kind
    }

    pub(crate) fn lexerdef(&self) -> &LRNonStreamingLexerDef<LexerTypesT> {
        &self.lexerdef
    }

    pub(crate) fn lexerdef_mut(&mut self) -> &mut LRNonStreamingLexerDef<LexerTypesT> {
        &mut self.lexerdef
    }

    pub(crate) fn set_rule_ids_map(
        &mut self,
        rule_ids_map: Option<HashMap<String, LexerTypesT::StorageT>>,
    ) {
        self.rule_ids_map = rule_ids_map;
    }

    fn gen_lex_flags(&self) -> TokenStream {
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
        } = self.lex_flags;
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

    fn gen_lexerdef(&self, token_stream: &mut TokenStream)
    where
        LexerTypesT: LexerTypes,
        LexerTypesT::StorageT: TryFrom<usize> + ToTokens,
        usize: num_traits::AsPrimitive<LexerTypesT::StorageT>,
    {
        let start_states = self.lexerdef.iter_start_states();
        let rules = self.lexerdef.iter_rules().map(|r| {
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
        token_stream.append_all(quote! {
            let start_states: Vec<StartState> = vec![#(#start_states),*];
            let rules = vec![#(#rules),*];
        });
    }

    fn gen_lexerkind(&self, token_stream: &mut TokenStream) -> TokenStream {
        let lexerdef_ty = match self.kind {
            LexerKind::LRNonStreamingLexer => {
                quote!(::lrlex::LRNonStreamingLexerDef)
            }
        };
        token_stream.append_all(quote! {
            #lexerdef_ty::from_rules(start_states, rules)
        });
        lexerdef_ty
    }

    fn gen_module(&self, lexerdef_func_impl: TokenStream, lexerdef_ty: TokenStream) -> TokenStream
    where
        LexerTypesT: LexerTypes,
        LexerTypesT::StorageT: ToTokens,
        usize: num_traits::AsPrimitive<LexerTypesT::StorageT>,
    {
        let mut token_consts = TokenStream::new();
        if let Some(rim) = &self.rule_ids_map {
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
        let token_consts = token_consts.into_iter();
        let lexerdef_param = str::parse::<TokenStream>(type_name::<LexerTypesT>()).unwrap();
        let mod_vis = &self.visibility;
        let mod_name = &self.mod_name;
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
    }

    fn gen_unformatted_source(&self, token_stream: TokenStream) -> String {
        token_stream.to_string()
    }

    fn gen_formatted_source(&self, unformatted: String, timestamp: &str) -> String {
        let mut outs = String::new();
        write!(outs, "// lrlex build time: {}\n\n", quote!(#timestamp),).ok();
        outs.push_str(
            &syn::parse_str(&unformatted)
                .map(|syntax_tree| prettyplease::unparse(&syntax_tree))
                .unwrap_or(unformatted),
        );
        outs
    }

    pub(crate) fn generate(&self, timestamp: &str) -> String
    where
        LexerTypesT::StorageT: ToTokens + TryFrom<usize>,
    {
        let mut lexerdef_func_impl = self.gen_lex_flags();
        self.gen_lexerdef(&mut lexerdef_func_impl);
        let lexerdef_ty = self.gen_lexerkind(&mut lexerdef_func_impl);
        let module_impl = self.gen_module(lexerdef_func_impl, lexerdef_ty);
        self.gen_formatted_source(self.gen_unformatted_source(module_impl), timestamp)
    }
}

#[derive(Debug, Clone)]
pub(crate) struct TokenMapCodegen<StorageT: Display + ToTokens> {
    mod_name: String,
    token_map: Vec<(String, TokenStream)>,
    rename_map: Option<HashMap<String, String>>,
    allow_dead_code: bool,
    _marker: PhantomData<StorageT>,
}

impl<StorageT: Display + ToTokens> TokenMapCodegen<StorageT> {
    pub(crate) fn new(
        mod_name: impl Into<String>,
        token_map: impl Borrow<HashMap<String, StorageT>>,
    ) -> Self {
        Self {
            mod_name: mod_name.into(),
            token_map: token_map
                .borrow()
                .iter()
                .map(|(tok_name, tok_value)| (tok_name.clone(), tok_value.to_token_stream()))
                .collect(),
            rename_map: None,
            allow_dead_code: false,
            _marker: PhantomData,
        }
    }
    pub(crate) fn rename_map<M, I, K, V>(mut self, rename_map: Option<M>) -> Self
    where
        M: IntoIterator<Item = I>,
        I: Borrow<(K, V)>,
        K: AsRef<str>,
        V: AsRef<str>,
    {
        self.rename_map = rename_map.map(|rename_map| {
            rename_map
                .into_iter()
                .map(|it| {
                    let (k, v) = it.borrow();
                    let k = k.as_ref().into();
                    let v = v.as_ref().into();
                    (k, v)
                })
                .collect()
        });
        self
    }

    pub(crate) fn allow_dead_code(mut self, allow_dead_code: bool) -> Self {
        self.allow_dead_code = allow_dead_code;
        self
    }

    pub(crate) fn generate(&self) -> Result<String, Box<dyn Error>> {
        // Record the time that this version of lrlex was built. If the source code changes and rustc
        // forces a recompile, this will change this value, causing anything which depends on this
        // build of lrlex to be recompiled too.
        let mut outs = String::new();
        let timestamp = env!("VERGEN_BUILD_TIMESTAMP");
        let mod_ident = format_ident!("{}", self.mod_name);
        write!(outs, "// lrlex build time: {}\n\n", quote!(#timestamp),).ok();
        let storaget = str::parse::<TokenStream>(type_name::<StorageT>()).unwrap();
        // Sort the tokens so that they're always in the same order.
        // This will prevent unneeded rebuilds.
        let mut token_map_sorted = self.token_map.clone();
        token_map_sorted.sort_by(|(l, _), (r, _)| l.cmp(r));
        let (token_array, tokens) = token_map_sorted
            .iter()
            .map(|(k, id)| {
                let name = match &self.rename_map {
                    Some(rmap) => rmap.get(k).unwrap_or(k),
                    _ => k,
                };
                let tok_ident: Ident = syn::parse_str(&format!("T_{}", name.to_ascii_uppercase()))
                    .map_err(|e| {
                        format!(
                            "token name {:?} is not a valid Rust identifier: {}; \
                            consider renaming it via `CTTokenMapBuilder::rename_map`.",
                            name, e
                        )
                    })?;
                Ok((
                    // Note: the array of all tokens can't use `tok_ident` because
                    // it will confuse the dead code checker. For this reason,
                    // we use `id` here.
                    quote! {
                        #id,
                    },
                    quote! {
                        pub const #tok_ident: #storaget = #id;
                    },
                ))
            })
            .collect::<Result<(TokenStream, TokenStream), Box<dyn Error>>>()?;
        let unused_annotation = if self.allow_dead_code {
            quote! {#[allow(dead_code)]}
        } else {
            quote! {}
        };
        // Since the formatter doesn't preserve comments and we don't want to lose build time,
        // just format the module contents.
        let unformatted = quote! {
            #unused_annotation
            mod #mod_ident {
                #tokens
                #[allow(dead_code)]
                pub const TOK_IDS: &[#storaget] = &[#token_array];
            }
        }
        .to_string();
        let out_mod = syn::parse_str(&unformatted)
            .map(|syntax_tree| prettyplease::unparse(&syntax_tree))
            .unwrap_or(unformatted);
        outs.push_str(&out_mod);
        Ok(outs)
    }

    pub(crate) fn mod_name(&self) -> &str {
        self.mod_name.as_str()
    }
}
/// Indents a multi-line string and trims any trailing newline.
/// This currently assumes that indentation on blank lines does not matter.
///
/// The algorithm used by this function is:
/// 1. Prefix `s` with the indentation, indenting the first line.
/// 2. Trim any trailing newlines.
/// 3. Replace all newlines with `\n{indent}`` to indent all lines after the first.
///
/// It is plausible that we should a step 4, but currently do not:
/// 4. Replace all `\n{indent}\n` with `\n\n`
fn indent(indent: &str, s: &str) -> String {
    format!("{indent}{}\n", s.trim_end_matches('\n')).replace('\n', &format!("\n{}", indent))
}

/// A string which uses `Display` for it's `Debug` impl.
struct ErrorString(String);
impl fmt::Display for ErrorString {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let ErrorString(s) = self;
        write!(f, "{}", s)
    }
}
impl fmt::Debug for ErrorString {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let ErrorString(s) = self;
        write!(f, "{}", s)
    }
}
impl Error for ErrorString {}

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
