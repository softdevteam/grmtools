use std::{
    any::type_name,
    fmt::{self, Write},
    hash::Hash,
    marker::PhantomData,
    path::Path,
};

use crate::{
    LexerTypes, RecoveryKind, RustEdition, SerialisationFormat, Visibility,
    ctbuilder::{FixIntConfig, VarIntConfig},
};

use cfgrammar::{
    Location, RIdx, Span, Symbol,
    header::{GrmtoolsSectionParser, Header, HeaderError, HeaderValue, RE_CRATE_DOT},
    markmap::MergeError,
    yacc::{
        YaccGrammar, YaccGrammarError, YaccKind, YaccOriginalActionKind, ast::ASTWithValidityInfo,
    },
};

use lrtable::{Minimiser, StateGraph, StateTable, StateTableError, from_yacc};
use proc_macro2::{Literal, TokenStream};
use quote::{ToTokens, TokenStreamExt, format_ident, quote};
use syn::{Generics, parse_quote};
use wincode::SchemaWrite;

const ACTION_PREFIX: &str = "__gt_";
const GLOBAL_PREFIX: &str = "__GT_";
const ACTIONS_KIND: &str = "__GtActionsKind";
const ACTIONS_KIND_PREFIX: &str = "Ak";
const ACTIONS_KIND_HIDDEN: &str = "__GtActionsKindHidden";

#[derive(Debug)]
#[non_exhaustive]
pub(crate) enum ParserSrcEnvError {
    GrmtoolsSectionParseError(Vec<HeaderError<Span>>),
    GrmtoolsSectionMergeError(MergeError<String, Box<HeaderValue<Location>>>),
    GrmtoolsSectionLookupError(HeaderError<Location>),
    MissingYaccKind,
    MissingModName,
}

#[derive(Debug)]
#[non_exhaustive]
pub(crate) enum ParserBuildEnvError<LexerTypesT>
where
    LexerTypesT: LexerTypes,
    usize: num_traits::AsPrimitive<LexerTypesT::StorageT>,
{
    StateTableError(StateTableError<LexerTypesT::StorageT>),
    YaccGrammarErrors(Vec<YaccGrammarError>),
    GrmtoolsSectionUnusedKeys(Vec<String>),
    GrmtoolsSectionMissingRequiredKeys(Vec<String>),
}

#[derive(Debug)]
#[non_exhaustive]
pub(crate) enum CodegenError {
    ProcMacro2Error(proc_macro2::LexError),
    InvalidRustIdentifierModName(syn::Error, String),
    InvalidParseGenerics(syn::Error),
    WincodeError(wincode::WriteError),
}

impl From<Vec<HeaderError<Span>>> for ParserSrcEnvError {
    fn from(it: Vec<HeaderError<Span>>) -> Self {
        ParserSrcEnvError::GrmtoolsSectionParseError(it)
    }
}

impl From<MergeError<String, Box<HeaderValue<Location>>>> for ParserSrcEnvError {
    fn from(it: MergeError<String, Box<HeaderValue<Location>>>) -> Self {
        ParserSrcEnvError::GrmtoolsSectionMergeError(it)
    }
}

impl From<HeaderError<Location>> for ParserSrcEnvError {
    fn from(it: HeaderError<Location>) -> Self {
        ParserSrcEnvError::GrmtoolsSectionLookupError(it)
    }
}

impl<LexerTypesT> From<Vec<YaccGrammarError>> for ParserBuildEnvError<LexerTypesT>
where
    LexerTypesT: LexerTypes,
    usize: num_traits::AsPrimitive<LexerTypesT::StorageT>,
{
    fn from(it: Vec<YaccGrammarError>) -> Self {
        ParserBuildEnvError::YaccGrammarErrors(it)
    }
}

impl<LexerTypesT> From<StateTableError<LexerTypesT::StorageT>> for ParserBuildEnvError<LexerTypesT>
where
    LexerTypesT: LexerTypes,
    usize: num_traits::AsPrimitive<LexerTypesT::StorageT>,
{
    fn from(it: StateTableError<LexerTypesT::StorageT>) -> Self {
        ParserBuildEnvError::StateTableError(it)
    }
}

impl From<proc_macro2::LexError> for CodegenError {
    fn from(it: proc_macro2::LexError) -> Self {
        CodegenError::ProcMacro2Error(it)
    }
}

impl From<wincode::WriteError> for CodegenError {
    fn from(it: wincode::WriteError) -> Self {
        CodegenError::WincodeError(it)
    }
}

impl fmt::Display for ParserSrcEnvError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&match self {
            Self::GrmtoolsSectionParseError(errs) => errs
                .iter()
                .map(|e| e.to_string())
                .collect::<Vec<_>>()
                .join("\n"),
            Self::GrmtoolsSectionMergeError(e) => e.to_string(),
            Self::GrmtoolsSectionLookupError(e) => e.to_string(),
            Self::MissingYaccKind => "Code generator cannot resolve yacc kind".to_string(),
            Self::MissingModName => "Code generator requires a mod name".to_string(),
        })
    }
}

impl<LexerTypesT> fmt::Display for ParserBuildEnvError<LexerTypesT>
where
    LexerTypesT: LexerTypes,
    usize: num_traits::AsPrimitive<LexerTypesT::StorageT>,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&match self {
            Self::StateTableError(e) => format!("{}", e).to_string(),
            Self::YaccGrammarErrors(errs) => errs
                .iter()
                .map(|e| e.to_string())
                .collect::<Vec<_>>()
                .join("\n"),
            Self::GrmtoolsSectionUnusedKeys(keys) => {
                format!("Unused keys in %grmtools section: {}", keys.join(", "))
            }
            Self::GrmtoolsSectionMissingRequiredKeys(keys) => format!(
                "Required keys are missing from %grmtools section: {}",
                keys.join(", ")
            ),
        })
    }
}
impl fmt::Display for CodegenError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&match self {
            Self::ProcMacro2Error(e) => e.to_string(),
            Self::InvalidRustIdentifierModName(e, s) => format!(
                "mod_name '{}' is not a valid rust identifier due to '{}'",
                s, e
            ),
            Self::InvalidParseGenerics(e) => format!("Unable to parse %parse-generics '{e}'"),
            Self::WincodeError(e) => format!("Unable to serialize parser {e}"),
        })
    }
}

pub(crate) struct ParserSrcEnv<'a, LexerTypesT>
where
    LexerTypesT: LexerTypes,
    usize: num_traits::AsPrimitive<LexerTypesT::StorageT>,
{
    src: &'a str,
    fallback_modname: Option<String>,
    grammar_path_cache_entry: Option<String>,
    header: Header<Location>,
    phantom: PhantomData<LexerTypesT::StorageT>,
}

pub(crate) struct ParserBuildEnvArgs<'a> {
    /// If the input came from a preparsed AST, this will be Some
    ast_with_validity_info: Option<&'a ASTWithValidityInfo>,
    mod_name: Option<String>,
    rust_edition: RustEdition,
    visibility: Visibility,
    error_on_conflicts: bool,
    show_warnings: bool,
    warnings_are_errors: bool,
}

pub(crate) struct ParserBuildEnv<'a, LexerTypesT>
where
    LexerTypesT: LexerTypes,
    usize: num_traits::AsPrimitive<LexerTypesT::StorageT>,
{
    ast_with_validity_info: ASTWithValidityInfo,
    recoverer: RecoveryKind,
    serialisation_format: SerialisationFormat,
    // Preserve the args for generating the cache.
    cache_args: ParserBuildEnvArgs<'a>,
    phantom_storaget: PhantomData<LexerTypesT::StorageT>,
    mod_name: String,
    grammar_path: Option<String>,
    header: Header<Location>,
}

pub(crate) struct ParserCodegen<LexerTypesT>
where
    LexerTypesT: LexerTypes,
    usize: num_traits::AsPrimitive<LexerTypesT::StorageT>,
{
    grm: YaccGrammar<LexerTypesT::StorageT>,
    stable: StateTable<LexerTypesT::StorageT>,
    sgraph: StateGraph<LexerTypesT::StorageT>,
    timestamp: String,
}

impl<'a> ParserBuildEnvArgs<'a> {
    pub(crate) fn new() -> Self {
        ParserBuildEnvArgs {
            ast_with_validity_info: None,
            mod_name: None,
            visibility: Visibility::Private,
            rust_edition: RustEdition::Rust2021,
            error_on_conflicts: true,
            show_warnings: true,
            warnings_are_errors: true,
        }
    }

    /// Set this to `Some(ast)` if the the parser should be built from a pre-parsed AST
    /// instead of from parsing a source string.
    pub(crate) fn ast_with_validity_info(mut self, ast: Option<&'a ASTWithValidityInfo>) -> Self {
        self.ast_with_validity_info = ast;
        self
    }

    pub(crate) fn mod_name(mut self, mod_name: Option<&str>) -> Self {
        self.mod_name = mod_name.map(|s| s.to_string());
        self
    }

    pub(crate) fn rust_edition(mut self, rust_edition: RustEdition) -> Self {
        self.rust_edition = rust_edition;
        self
    }
    pub(crate) fn visibility(mut self, visibility: Visibility) -> Self {
        self.visibility = visibility;
        self
    }
    pub(crate) fn error_on_conflicts(mut self, error_on_conflicts: bool) -> Self {
        self.error_on_conflicts = error_on_conflicts;
        self
    }
    pub(crate) fn show_warnings(mut self, show_warnings: bool) -> Self {
        self.show_warnings = show_warnings;
        self
    }
    pub(crate) fn warnings_are_errors(mut self, warnings_are_errors: bool) -> Self {
        self.warnings_are_errors = warnings_are_errors;
        self
    }
}

impl<'a, LexerTypesT> ParserSrcEnv<'a, LexerTypesT>
where
    LexerTypesT: LexerTypes,
    usize: num_traits::AsPrimitive<LexerTypesT::StorageT>,
{
    pub(crate) fn new_with_header(
        src: &'a str,
        path: Option<&Path>,
        header: Header<Location>,
    ) -> ParserSrcEnv<'a, LexerTypesT> {
        let fallback_modname = if let Some(path) = path {
            // When the user hasn't specified a module name, so we create one automatically: what we
            // do is strip off all the filename extensions (note that it's likely that inp ends
            // with `y.rs`, so we potentially have to strip off more than one extension) and
            // then add `_y` to the end.
            let mut stem = path.to_str().unwrap();
            loop {
                let new_stem = Path::new(stem).file_stem().unwrap().to_str().unwrap();
                if stem == new_stem {
                    break;
                }
                stem = new_stem;
            }
            Some(format!("{}_y", stem))
        } else {
            None
        };
        let grammar_path_cache_entry = path.map(|s| s.to_string_lossy().to_string());
        ParserSrcEnv {
            src,
            fallback_modname,
            grammar_path_cache_entry,
            header,
            phantom: PhantomData,
        }
    }

    fn merge_headers(&mut self) -> Result<(), ParserSrcEnvError> {
        let (parsed_header, _) = self.parse_header()?;
        Ok(self.header.merge_from(parsed_header)?)
    }

    fn parse_header(&self) -> Result<(Header<Span>, usize), Vec<HeaderError<Span>>> {
        GrmtoolsSectionParser::new(self.src, false).parse()
    }

    /// Looks up the `yacckind` field from the header, marks the field
    /// as used then constructs AST of that kind.
    fn resolve_ast_with_validity_info(
        &mut self,
        from_ast: Option<&ASTWithValidityInfo>,
    ) -> Result<ASTWithValidityInfo, ParserSrcEnvError> {
        self.header.mark_used(&"cfgrammar.yacckind".to_string());
        if let Some(ast) = from_ast {
            Ok(ast.clone())
        } else if let Some(yk) = self
            .header
            .get("cfgrammar.yacckind")
            .map(|HeaderValue(_, val)| val)
            .map(YaccKind::try_from)
            .transpose()?
        {
            Ok(ASTWithValidityInfo::new(yk, self.src))
        } else {
            Err(ParserSrcEnvError::MissingYaccKind)?
        }
    }

    /// Looks up the `recoverer` field in the header, marks the field
    /// as used, and defaulting to `CPCTPlus` if unfound.
    fn resolve_recoverer(&mut self) -> Result<RecoveryKind, ParserSrcEnvError> {
        self.header.mark_used(&"lrpar.recoverer".to_string());
        let rk_val = self
            .header
            .get("lrpar.recoverer")
            .map(|HeaderValue(_, rk_val)| rk_val);
        if let Some(rk_val) = rk_val {
            Ok(RecoveryKind::try_from(rk_val)?)
        } else {
            // Fallback to the default recoverykind.
            Ok(RecoveryKind::CPCTPlus)
        }
    }

    /// Looks up the `serialisation_format` field in the header, marks the field
    /// as used, and defaults to `VariableSizedInteger` if unfound.
    fn resolve_serialisation_format(&mut self) -> Result<SerialisationFormat, ParserSrcEnvError> {
        self.header
            .mark_used(&"lrpar.serialisation_format".to_string());
        if let Some(ec_val) = self
            .header
            .get("lrpar.serialisation_format")
            .map(|HeaderValue(_, ec_val)| ec_val)
        {
            Ok(SerialisationFormat::try_from(ec_val)?)
        } else {
            Ok(SerialisationFormat::VariableSizedInteger)
        }
    }

    /// Looks up the `mod_name` from the `args`, and defaults to
    /// the `{filename}_y` with any file extenstion stripped off.
    fn resolve_mod_name(&self, args: &ParserBuildEnvArgs) -> Result<String, ParserSrcEnvError> {
        match &args.mod_name {
            Some(s) => Ok(s.to_owned()),
            None => self
                .fallback_modname
                .as_ref()
                .ok_or(ParserSrcEnvError::MissingModName)
                .map(|s| s.to_string()),
        }
    }

    pub(crate) fn build_env(
        mut self,
        args: ParserBuildEnvArgs<'a>,
    ) -> Result<ParserBuildEnv<'a, LexerTypesT>, ParserSrcEnvError>
    where
        LexerTypesT: LexerTypes,
        usize: num_traits::AsPrimitive<LexerTypesT::StorageT>,
    {
        self.merge_headers()?;
        let ast_with_validity_info =
            self.resolve_ast_with_validity_info(args.ast_with_validity_info)?;
        let recoverer = self.resolve_recoverer()?;
        let serialisation_format = self.resolve_serialisation_format()?;
        let mod_name = self.resolve_mod_name(&args)?;
        let grammar_path = self.grammar_path_cache_entry;

        Ok(ParserBuildEnv {
            ast_with_validity_info,
            cache_args: args,
            recoverer,
            serialisation_format,
            mod_name,
            grammar_path,
            header: self.header,
            phantom_storaget: PhantomData,
        })
    }
}

impl<'a, LexerTypesT> ParserBuildEnv<'a, LexerTypesT>
where
    LexerTypesT: LexerTypes,
    usize: num_traits::AsPrimitive<LexerTypesT::StorageT>,
{
    pub(crate) fn ast_with_validity_info(&self) -> &ASTWithValidityInfo {
        &self.ast_with_validity_info
    }

    pub(crate) fn header_mut(&mut self) -> &mut Header<Location> {
        &mut self.header
    }

    pub(crate) fn serialisation_format(&self) -> &SerialisationFormat {
        &self.serialisation_format
    }

    pub(crate) fn derived_mod_name(&self) -> &str {
        &self.mod_name
    }

    pub(crate) fn specified_mod_name(&self) -> Option<&str> {
        self.cache_args.mod_name.as_deref()
    }

    pub(crate) fn recoverer(&self) -> RecoveryKind {
        self.recoverer
    }

    pub(crate) fn rust_edition(&self) -> RustEdition {
        self.cache_args.rust_edition
    }

    pub(crate) fn visibility(&self) -> &Visibility {
        &self.cache_args.visibility
    }

    pub(crate) fn show_warnings(&self) -> bool {
        self.cache_args.show_warnings
    }

    pub(crate) fn warnings_are_errors(&self) -> bool {
        self.cache_args.warnings_are_errors
    }

    pub(crate) fn error_on_conflicts(&self) -> bool {
        self.cache_args.error_on_conflicts
    }

    pub(crate) fn yacc_kind(&self) -> YaccKind {
        self.ast_with_validity_info.yacc_kind()
    }

    /// Returns an error if any unused keys specified in a `%grmtools` directive that begin with a
    /// `crate_name.` prefix for `crate_name` value are found. If the `crate_name` is None returns
    ///  an error if any unused keys with no crate prefix specified are found.
    pub(crate) fn check_unused_header_keys_for_crate(
        &self,
        crate_name: Option<&str>,
    ) -> Result<(), ParserBuildEnvError<LexerTypesT>> {
        let unused_keys = self
            .header
            .unused()
            .iter()
            .filter(|(s, _)| {
                if let Some(crate_name) = crate_name {
                    s.starts_with(&format!("{crate_name}."))
                } else {
                    !RE_CRATE_DOT.is_match(s)
                }
            })
            .map(|(s, _)| s.to_string())
            .collect::<Vec<_>>();
        if !unused_keys.is_empty() {
            return Err(ParserBuildEnvError::GrmtoolsSectionUnusedKeys(unused_keys));
        }
        let missing_keys = self
            .header
            .missing()
            .iter()
            .map(|s| s.to_string())
            .collect::<Vec<_>>();
        if !missing_keys.is_empty() {
            Err(ParserBuildEnvError::GrmtoolsSectionMissingRequiredKeys(
                missing_keys,
            ))
        } else {
            Ok(())
        }
    }

    pub(crate) fn code_generator(
        &self,
        timestamp: &str,
    ) -> Result<ParserCodegen<LexerTypesT>, ParserBuildEnvError<LexerTypesT>> {
        let grm = YaccGrammar::<LexerTypesT::StorageT>::new_from_ast_with_validity_info(
            &self.ast_with_validity_info,
        )?;
        let (sgraph, stable) = from_yacc(&grm, Minimiser::Pager)?;
        Ok(ParserCodegen {
            grm,
            stable,
            sgraph,
            timestamp: timestamp.to_string(),
        })
    }
}

impl<LexerTypesT> ParserCodegen<LexerTypesT>
where
    LexerTypesT: LexerTypes,
    usize: num_traits::AsPrimitive<LexerTypesT::StorageT>,
    LexerTypesT::StorageT: 'static
        + fmt::Debug
        + Hash
        + num_traits::PrimInt
        + SchemaWrite<FixIntConfig, Src = LexerTypesT::StorageT>
        + SchemaWrite<VarIntConfig, Src = LexerTypesT::StorageT>
        + num_traits::Unsigned,
    LexerTypesT: LexerTypes,
{
    pub(crate) fn grm(&self) -> &YaccGrammar<LexerTypesT::StorageT> {
        &self.grm
    }

    pub(crate) fn stable(&self) -> &StateTable<LexerTypesT::StorageT> {
        &self.stable
    }

    pub(crate) fn sgraph(&self) -> &StateGraph<LexerTypesT::StorageT> {
        &self.sgraph
    }

    pub(crate) fn finish(
        self,
    ) -> (
        YaccGrammar<LexerTypesT::StorageT>,
        StateGraph<LexerTypesT::StorageT>,
        StateTable<LexerTypesT::StorageT>,
    ) {
        (self.grm, self.sgraph, self.stable)
    }

    pub(crate) fn generate(
        &self,
        build_env: &ParserBuildEnv<LexerTypesT>,
    ) -> Result<String, CodegenError> {
        let mod_name = build_env.derived_mod_name();
        let visibility = build_env.visibility();
        let user_actions = if let YaccKind::Original(YaccOriginalActionKind::UserAction)
        | YaccKind::Grmtools = build_env.yacc_kind()
        {
            Some(self.gen_user_actions()?)
        } else {
            None
        };
        let rule_consts = self.gen_rule_consts()?;
        let token_epp = self.gen_token_epp()?;
        let parse_function = self.gen_parse_function(build_env)?;
        let action_wrappers = match build_env.yacc_kind() {
            YaccKind::Original(YaccOriginalActionKind::UserAction) | YaccKind::Grmtools => {
                Some(self.gen_wrappers(build_env)?)
            }
            YaccKind::Original(YaccOriginalActionKind::NoAction)
            | YaccKind::Original(YaccOriginalActionKind::GenericParseTree) => None,
            _ => unreachable!(),
        };

        let additional_decls = if let YaccKind::Original(YaccOriginalActionKind::GenericParseTree) =
            build_env.yacc_kind()
        {
            // `lrpar::Node`` is deprecated within the lrpar crate, but not from within this module,
            // Once it is removed from `lrpar`, we should move the declaration here entirely.
            Some(quote! {
                #[allow(unused_imports)]
                pub use ::lrpar::parser::_deprecated_moved_::Node;
            })
        } else {
            None
        };

        let mod_name = match syn::parse_str::<proc_macro2::Ident>(mod_name) {
            Ok(s) => s,
            Err(e) => {
                return Err(CodegenError::InvalidRustIdentifierModName(
                    e,
                    mod_name.to_string(),
                ));
            }
        };
        let out_tokens = quote! {
            #visibility mod #mod_name {
                // At the top so that `user_actions` may contain #![inner_attribute]
                #user_actions
                mod _parser_ {
                    #![allow(clippy::type_complexity)]
                    #![allow(clippy::unnecessary_wraps)]
                    #![deny(unsafe_code)]
                    #[allow(unused_imports)]
                    use super::*;
                    #additional_decls
                    #parse_function
                    #rule_consts
                    #token_epp
                    #action_wrappers
                } // End of `mod _parser_`
                #[allow(unused_imports)]
                pub use _parser_::*;
                #[allow(unused_imports)]
                use ::lrpar::Lexeme;
            } // End of `mod #mod_name`
        };
        // Try and run a code formatter on the generated code.
        let unformatted = out_tokens.to_string();
        Ok(syn::parse_str(&unformatted)
            .map(|syntax_tree| prettyplease::unparse(&syntax_tree))
            .unwrap_or(unformatted))
    }

    /// Generate the cache, which determines if anything's changed enough that we need to
    /// regenerate outputs and force rustc to recompile.
    fn gen_cache(&self, build_env: &ParserBuildEnv<LexerTypesT>) -> TokenStream {
        let grm = self.grm();
        let build_time = &self.timestamp;
        let grammar_path = &build_env.grammar_path;
        let mod_name = QuoteOption(build_env.specified_mod_name());
        let visibility = build_env.visibility().to_variant_tokens();
        let rust_edition = build_env.rust_edition().to_variant_tokens();
        let yacckind = build_env.yacc_kind();
        let rule_map = grm
            .iter_tidxs()
            .map(|tidx| {
                QuoteTuple((
                    usize::from(tidx),
                    grm.token_name(tidx).unwrap_or("<unknown>"),
                ))
            })
            .collect::<Vec<_>>();
        let derived_mod_name = build_env.derived_mod_name();
        let serialisation_format = build_env.serialisation_format();
        let recoverer = build_env.recoverer();
        let error_on_conflicts = build_env.error_on_conflicts();
        let show_warnings = build_env.show_warnings();
        let warnings_are_errors = build_env.warnings_are_errors();
        let cache_info = quote! {
            BUILD_TIME = #build_time
            DERIVED_MOD_NAME = #derived_mod_name
            ENCODING_CONFIG = #serialisation_format
            GRAMMAR_PATH = #grammar_path
            MOD_NAME = #mod_name
            RECOVERER = #recoverer
            YACC_KIND = #yacckind
            ERROR_ON_CONFLICTS = #error_on_conflicts
            SHOW_WARNINGS = #show_warnings
            WARNINGS_ARE_ERRORS = #warnings_are_errors
            RUST_EDITION = #rust_edition
            RULE_IDS_MAP = [#(#rule_map,)*]
            VISIBILITY = #visibility
        };
        let cache_info_str = cache_info.to_string();
        quote!(#cache_info_str)
    }

    pub(crate) fn cache_str(&self, build_env: &ParserBuildEnv<LexerTypesT>) -> String {
        self.gen_cache(build_env).to_string()
    }

    /// Generate the user action functions (if any).
    fn gen_user_actions(&self) -> Result<TokenStream, CodegenError> {
        let grm = self.grm();
        let programs = grm
            .programs()
            .as_ref()
            .map(|s| str::parse::<TokenStream>(s))
            .transpose()?;
        let mut action_fns = TokenStream::new();
        // Convert actions to functions
        let parsed_parse_generics = make_generics(grm.parse_generics().as_deref())?;
        let (generics, _, where_clause) = parsed_parse_generics.split_for_impl();
        let (parse_paramname, parse_paramdef, parse_param_unit);
        match grm.parse_param() {
            Some((name, tyname)) => {
                parse_param_unit = tyname.trim() == "()";
                parse_paramname = str::parse::<TokenStream>(name)?;
                let ty = str::parse::<TokenStream>(tyname)?;
                parse_paramdef = quote!(#parse_paramname: #ty);
            }
            None => {
                parse_param_unit = true;
                parse_paramname = quote!(());
                parse_paramdef = quote! {_: ()};
            }
        };
        for pidx in grm.iter_pidxs() {
            if pidx == grm.start_prod() {
                continue;
            }

            // Work out the right type for each argument
            let mut args = Vec::with_capacity(grm.prod(pidx).len());
            for i in 0..grm.prod(pidx).len() {
                let argt = match grm.prod(pidx)[i] {
                    Symbol::Rule(ref_ridx) => {
                        let action_type = grm.actiontype(ref_ridx)
                           .as_ref()
                           .expect("actiontype should have been checked during complete_and_validate for this YaccKind");
                        str::parse::<TokenStream>(action_type)?
                    }
                    Symbol::Token(_) => {
                        let lexemet =
                            str::parse::<TokenStream>(type_name::<LexerTypesT::LexemeT>())?;
                        quote!(::std::result::Result<#lexemet, #lexemet>)
                    }
                };
                let arg = format_ident!("{}arg_{}", ACTION_PREFIX, i + 1);
                args.push(quote!(mut #arg: #argt));
            }

            // If this rule's `actiont` is `()` then Clippy will warn that the return type `-> ()`
            // is pointless (which is true). We therefore avoid outputting a return type if actiont
            // is the unit type.
            let returnt = {
                let actiont = grm.actiontype(grm.prod_to_rule(pidx)).as_ref().unwrap();
                if actiont == "()" {
                    None
                } else {
                    let actiont = str::parse::<TokenStream>(actiont)?;
                    Some(quote!( -> #actiont))
                }
            };
            let action_fn = format_ident!("{}action_{}", ACTION_PREFIX, usize::from(pidx));
            let lexer_var = format_ident!("{}lexer", ACTION_PREFIX);
            let span_var = format_ident!("{}span", ACTION_PREFIX);
            let ridx_var = format_ident!("{}ridx", ACTION_PREFIX);
            let storaget = str::parse::<TokenStream>(type_name::<LexerTypesT::StorageT>())?;
            let lexertypest = str::parse::<TokenStream>(type_name::<LexerTypesT>())?;
            let bind_parse_param = if !parse_param_unit {
                Some(quote! {let _ = #parse_paramname;})
            } else {
                None
            };

            // Iterate over all $-arguments and replace them with their respective
            // element from the argument vector (e.g. $1 is replaced by args[0]).
            let pre_action = grm.action(pidx).as_ref().expect("action code should have been checked during complete_and_validate for this YaccKind");
            let mut last = 0;
            let mut outs = String::new();
            loop {
                match pre_action[last..].find('$') {
                    Some(off) => {
                        if pre_action[last + off..].starts_with("$$") {
                            outs.push_str(&pre_action[last..last + off + "$".len()]);
                            last = last + off + "$$".len();
                        } else if pre_action[last + off..].starts_with("$lexer") {
                            outs.push_str(&pre_action[last..last + off]);
                            write!(outs, "{prefix}lexer", prefix = ACTION_PREFIX).ok();
                            last = last + off + "$lexer".len();
                        } else if pre_action[last + off..].starts_with("$span") {
                            outs.push_str(&pre_action[last..last + off]);
                            write!(outs, "{prefix}span", prefix = ACTION_PREFIX).ok();
                            last = last + off + "$span".len();
                        } else if last + off + 1 < pre_action.len()
                            && pre_action[last + off + 1..].starts_with(|c: char| c.is_numeric())
                        {
                            outs.push_str(&pre_action[last..last + off]);
                            write!(outs, "{prefix}arg_", prefix = ACTION_PREFIX).ok();
                            last = last + off + "$".len();
                        } else {
                            unreachable!("action variables checked during complete_and_validate");
                        }
                    }
                    None => {
                        outs.push_str(&pre_action[last..]);
                        break;
                    }
                }
            }

            let action_body = str::parse::<TokenStream>(&outs)?;
            action_fns.extend(quote! {
                #[allow(clippy::too_many_arguments)]
                fn #action_fn #generics (
                    #ridx_var: ::cfgrammar::RIdx<#storaget>,
                    #lexer_var: &'lexer dyn ::lrpar::NonStreamingLexer<'input, #lexertypest>,
                    #span_var: ::cfgrammar::Span,
                    #parse_paramdef,
                    #(#args,)*
                ) #returnt
                #where_clause
                {
                    #bind_parse_param
                    #action_body
                }
            })
        }
        Ok(quote! {
            #programs
            #action_fns
        })
    }

    fn gen_rule_consts(&self) -> Result<TokenStream, proc_macro2::LexError> {
        let grm = self.grm();
        let mut toks = TokenStream::new();
        for ridx in grm.iter_rules() {
            if !grm.rule_to_prods(ridx).contains(&grm.start_prod()) {
                let r_const = format_ident!("R_{}", grm.rule_name_str(ridx).to_ascii_uppercase());
                let storage_ty = str::parse::<TokenStream>(type_name::<LexerTypesT::StorageT>())?;
                let ridx = UnsuffixedUsize(usize::from(ridx));
                toks.extend(quote! {
                    #[allow(dead_code)]
                    pub const #r_const: #storage_ty = #ridx;
                });
            }
        }
        Ok(toks)
    }

    fn gen_token_epp(&self) -> Result<TokenStream, proc_macro2::LexError> {
        let grm = self.grm();
        let mut tidxs = Vec::new();
        for tidx in grm.iter_tidxs() {
            tidxs.push(QuoteOption(grm.token_epp(tidx)));
        }
        let const_epp_ident = format_ident!("{}EPP", GLOBAL_PREFIX);
        let storage_ty = str::parse::<TokenStream>(type_name::<LexerTypesT::StorageT>())?;
        Ok(quote! {
            const #const_epp_ident: &[::std::option::Option<&str>] = &[
                #(#tidxs,)*
            ];

            /// Return the %epp entry for token `tidx` (where `None` indicates \"the token has no
            /// pretty-printed value\"). Panics if `tidx` doesn't exist.
            #[allow(dead_code)]
            pub fn token_epp<'a>(tidx: ::cfgrammar::TIdx<#storage_ty>) -> ::std::option::Option<&'a str> {
                #const_epp_ident[usize::from(tidx)]
            }
        })
    }

    /// Generate the main parse() function for the output file.
    fn gen_parse_function(
        &self,
        build_env: &ParserBuildEnv<LexerTypesT>,
    ) -> Result<TokenStream, CodegenError> {
        let stable = self.stable();
        let grm = self.grm();
        let storaget = str::parse::<TokenStream>(type_name::<LexerTypesT::StorageT>())?;
        let lexertypest = str::parse::<TokenStream>(type_name::<LexerTypesT>())?;
        let recoverer = build_env.recoverer();
        let run_parser = match build_env.yacc_kind() {
            YaccKind::Original(YaccOriginalActionKind::GenericParseTree) => {
                quote! {
                    ::lrpar::RTParserBuilder::new(grm, stable)
                        .recoverer(#recoverer)
                        .parse_map(
                            lexer,
                            &|lexeme| Node::Term{lexeme},
                            &|ridx, nodes| Node::Nonterm{ridx, nodes}
                        )
                }
            }
            YaccKind::Original(YaccOriginalActionKind::NoAction) => {
                quote! {
                    ::lrpar::RTParserBuilder::new(grm, stable)
                        .recoverer(#recoverer)
                        .parse_map(lexer, &|_| (), &|_, _| ()).1
                }
            }
            YaccKind::Original(YaccOriginalActionKind::UserAction) | YaccKind::Grmtools => {
                let actionskind = str::parse::<TokenStream>(ACTIONS_KIND)?;
                let parsed_parse_generics = make_generics(grm.parse_generics().as_deref())?;
                let (_, type_generics, _) = parsed_parse_generics.split_for_impl();
                // actions always have a parse_param argument, and when the `parse` function lacks one
                // that parameter will be unit.
                let (action_fn_parse_param, action_fn_parse_param_ty) = match grm.parse_param() {
                    Some((name, ty)) => {
                        let name = str::parse::<TokenStream>(name)?;
                        let ty = str::parse::<TokenStream>(ty)?;
                        (quote!(#name), quote!(#ty))
                    }
                    None => (quote!(()), quote!(())),
                };
                let wrappers = grm.iter_pidxs().map(|pidx| {
                    let pidx = usize::from(pidx);
                    format_ident!("{}wrapper_{}", ACTION_PREFIX, pidx)
                });
                let edition_lifetime = if build_env.rust_edition() != RustEdition::Rust2015 {
                    quote!('_,)
                } else {
                    quote!()
                };
                let ridx = usize::from(self.user_start_ridx());
                let action_ident = format_ident!("{}{}", ACTIONS_KIND_PREFIX, ridx);

                quote! {
                    let actions: ::std::vec::Vec<
                            &dyn Fn(
                                    ::cfgrammar::RIdx<#storaget>,
                                    &'lexer dyn ::lrpar::NonStreamingLexer<'input, #lexertypest>,
                                    ::cfgrammar::Span,
                                    ::std::vec::Drain<#edition_lifetime ::lrpar::parser::AStackType<<#lexertypest as ::lrpar::LexerTypes>::LexemeT, #actionskind #type_generics>>,
                                    #action_fn_parse_param_ty
                            ) -> #actionskind #type_generics
                        > = ::std::vec![#(&#wrappers,)*];
                    match ::lrpar::RTParserBuilder::new(grm, stable)
                        .recoverer(#recoverer)
                        .parse_actions(lexer, &actions, #action_fn_parse_param) {
                            (Some(#actionskind::#action_ident(x)), y) => (Some(x), y),
                            (None, y) => (None, y),
                            _ => unreachable!()
                    }
                }
            }
            kind => panic!("YaccKind {:?} not supported", kind),
        };

        let parsed_parse_generics: Generics = match build_env.yacc_kind() {
            YaccKind::Original(YaccOriginalActionKind::UserAction) | YaccKind::Grmtools => {
                make_generics(grm.parse_generics().as_deref())?
            }
            _ => make_generics(None)?,
        };
        let (generics, _, where_clause) = parsed_parse_generics.split_for_impl();

        // `parse()` may or may not have an argument for `%parseparam`.
        let parse_fn_parse_param = match build_env.yacc_kind() {
            YaccKind::Original(YaccOriginalActionKind::UserAction) | YaccKind::Grmtools => {
                if let Some((name, tyname)) = grm.parse_param() {
                    let name = str::parse::<TokenStream>(name)?;
                    let tyname = str::parse::<TokenStream>(tyname)?;
                    Some(quote! {#name: #tyname})
                } else {
                    None
                }
            }
            _ => None,
        };
        let parse_fn_return_ty = match build_env.yacc_kind() {
            YaccKind::Original(YaccOriginalActionKind::UserAction) | YaccKind::Grmtools => {
                let actiont = grm
                    .actiontype(self.user_start_ridx())
                    .as_ref()
                    .map(|at| str::parse::<TokenStream>(at))
                    .transpose()?;
                quote! {
                    (::std::option::Option<#actiont>, ::std::vec::Vec<::lrpar::LexParseError<#storaget, #lexertypest>>)
                }
            }
            YaccKind::Original(YaccOriginalActionKind::GenericParseTree) => quote! {
                (::std::option::Option<Node<<#lexertypest as ::lrpar::LexerTypes>::LexemeT, #storaget>>,
                    ::std::vec::Vec<::lrpar::LexParseError<#storaget, #lexertypest>>)
            },
            YaccKind::Original(YaccOriginalActionKind::NoAction) => quote! {
                ::std::vec::Vec<::lrpar::LexParseError<#storaget, #lexertypest>>
            },
            _ => unreachable!(),
        };

        let serialisation_format = build_env.serialisation_format();
        // Note that the configuration types use associated consts, and thus these configurations represent distinct types.
        let (grm_data, stable_data): (Vec<u8>, Vec<u8>) = match serialisation_format {
            SerialisationFormat::FixedSizeInteger => {
                let config = wincode::config::Configuration::default().with_fixint_encoding();
                let grm = wincode::config::serialize(grm, config)?;
                let stable = wincode::config::serialize(stable, config)?;
                (grm, stable)
            }
            SerialisationFormat::VariableSizedInteger => {
                let config = wincode::config::Configuration::default().with_varint_encoding();
                let grm = wincode::config::serialize(grm, config)?;
                let stable = wincode::config::serialize(stable, config)?;
                (grm, stable)
            }
        };
        let serialisation_format_str = quote!(serialisation_format).to_string();
        Ok(quote! {
            const __GRM_DATA: &[u8] = &[#(#grm_data,)*];
            const __STABLE_DATA: &[u8] = &[#(#stable_data,)*];
            const __SERIALISATION_FORMAT: ::lrpar::ctbuilder::SerialisationFormat = #serialisation_format;

            fn __lrpar_parser_data() -> &'static ::lrpar::ParserData<#storaget> {
                static DATA: ::std::sync::OnceLock<::lrpar::ParserData<#storaget>>
                    = ::std::sync::OnceLock::new();
                DATA.get_or_init(
                    || {
                        // We have to call reconstitute like this because the config parameter takes a trait
                        // which uses const generics. Thus the two config parameters here are not actually of the same type.
                        match __SERIALISATION_FORMAT {
                            ::lrpar::ctbuilder::SerialisationFormat::FixedSizeInteger => {
                                ::lrpar::ctbuilder::_reconstitute(__GRM_DATA, __STABLE_DATA, ::lrpar::ctbuilder::wincode::config::Configuration::default().with_fixint_encoding())
                            }
                            ::lrpar::ctbuilder::SerialisationFormat::VariableSizedInteger => {
                                ::lrpar::ctbuilder::_reconstitute(__GRM_DATA, __STABLE_DATA, ::lrpar::ctbuilder::wincode::config::Configuration::default().with_varint_encoding())
                            }
                            _ => {
                                panic!("Parser source was generated using unknown `SerialisationFormat`: {:?}", #serialisation_format_str)
                            }
                        }
                    }
                )
            }

            #[allow(dead_code)]
            pub fn parse #generics (
                 lexer: &'lexer dyn ::lrpar::NonStreamingLexer<'input, #lexertypest>,
                 #parse_fn_parse_param
            ) -> #parse_fn_return_ty
            #where_clause
            {
                let __data = __lrpar_parser_data();
                let grm = __data.grm();
                let stable = __data.stable();
                #run_parser
            }
        })
    }

    /// Generate the wrappers that call user actions
    fn gen_wrappers(
        &self,
        build_env: &ParserBuildEnv<LexerTypesT>,
    ) -> Result<TokenStream, CodegenError> {
        let grm = self.grm();
        let parsed_parse_generics = make_generics(grm.parse_generics().as_deref())?;
        let (generics, type_generics, where_clause) = parsed_parse_generics.split_for_impl();

        let (parse_paramname, parse_paramdef);
        match grm.parse_param() {
            Some((name, tyname)) => {
                parse_paramname = str::parse::<TokenStream>(name)?;
                let ty = str::parse::<TokenStream>(tyname)?;
                parse_paramdef = quote!(#parse_paramname: #ty);
            }
            None => {
                parse_paramname = quote!(());
                parse_paramdef = quote! {_: ()};
            }
        };

        let mut wrappers = TokenStream::new();
        for pidx in grm.iter_pidxs() {
            let ridx = grm.prod_to_rule(pidx);

            // Iterate over all $-arguments and replace them with their respective
            // element from the argument vector (e.g. $1 is replaced by args[0]). At
            // the same time extract &str from tokens and actiontype from nonterminals.
            let wrapper_fn = format_ident!("{}wrapper_{}", ACTION_PREFIX, usize::from(pidx));
            let ridx_var = format_ident!("{}ridx", ACTION_PREFIX);
            let lexer_var = format_ident!("{}lexer", ACTION_PREFIX);
            let span_var = format_ident!("{}span", ACTION_PREFIX);
            let args_var = format_ident!("{}args", ACTION_PREFIX);
            let storaget = str::parse::<TokenStream>(type_name::<LexerTypesT::StorageT>())?;
            let lexertypest = str::parse::<TokenStream>(type_name::<LexerTypesT>())?;
            let actionskind = str::parse::<TokenStream>(ACTIONS_KIND)?;
            let edition_lifetime = if build_env.rust_edition() != RustEdition::Rust2015 {
                Some(quote!('_,))
            } else {
                None
            };
            let mut wrapper_fn_body = TokenStream::new();
            if grm.action(pidx).is_some() {
                // Unpack the arguments passed to us by the drain
                for i in 0..grm.prod(pidx).len() {
                    let arg = format_ident!("{}arg_{}", ACTION_PREFIX, i + 1);
                    wrapper_fn_body.extend(match grm.prod(pidx)[i] {
                        Symbol::Rule(ref_ridx) => {
                            let ref_ridx = usize::from(ref_ridx);
                            let actionvariant = format_ident!("{}{}", ACTIONS_KIND_PREFIX, ref_ridx);
                            quote! {
                                #[allow(clippy::let_unit_value)]
                                let #arg = match #args_var.next().unwrap() {
                                    ::lrpar::parser::AStackType::ActionType(#actionskind::#type_generics::#actionvariant(x)) => x,
                                    _ => unreachable!()
                                };
                            }
                        }
                        Symbol::Token(_) => {
                            quote! {
                                let #arg = match #args_var.next().unwrap() {
                                    ::lrpar::parser::AStackType::Lexeme(l) => {
                                        if l.faulty() {
                                            Err(l)
                                        } else {
                                            Ok(l)
                                        }
                                    },
                                    ::lrpar::parser::AStackType::ActionType(_) => unreachable!()
                                };
                            }
                        }
                    })
                }

                // Call the user code
                let args = (0..grm.prod(pidx).len())
                    .map(|i| format_ident!("{}arg_{}", ACTION_PREFIX, i + 1))
                    .collect::<Vec<_>>();
                let action_fn = format_ident!("{}action_{}", ACTION_PREFIX, usize::from(pidx));
                let actionsvariant = format_ident!("{}{}", ACTIONS_KIND_PREFIX, usize::from(ridx));

                wrapper_fn_body.extend(match grm.actiontype(ridx) {
                    Some(s) if s == "()" => {
                        // If the rule `r` that we're calling has the unit type then Clippy will warn that
                        // `enum::A(wrapper_r())` is pointless. We thus have to split it into two:
                        // `wrapper_r(); enum::A(())`.
                        quote! {
                            #action_fn(#ridx_var, #lexer_var, #span_var, #parse_paramname, #(#args,)*);
                            #actionskind::#type_generics::#actionsvariant(())
                        }
                    }
                    _ => {
                        quote! {
                            #actionskind::#type_generics::#actionsvariant(#action_fn(#ridx_var, #lexer_var, #span_var, #parse_paramname, #(#args,)*))
                        }
                    }
                })
            } else if pidx == grm.start_prod() {
                wrapper_fn_body.extend(quote!(unreachable!()));
            } else {
                unreachable!(
                    "Production in rule '{}' must have an action body, which should have been handled by gen_user_actions.",
                    grm.rule_name_str(grm.prod_to_rule(pidx))
                );
            };

            let attrib = if pidx == grm.start_prod() {
                // The start prod has an unreachable body so it doesn't use it's variables.
                Some(quote!(#[allow(unused_variables)]))
            } else {
                None
            };
            wrappers.extend(quote! {
                #attrib
                fn #wrapper_fn #generics (
                    #ridx_var: ::cfgrammar::RIdx<#storaget>,
                    #lexer_var: &'lexer dyn ::lrpar::NonStreamingLexer<'input, #lexertypest>,
                    #span_var: ::cfgrammar::Span,
                    mut #args_var: ::std::vec::Drain<#edition_lifetime ::lrpar::parser::AStackType<<#lexertypest as ::lrpar::LexerTypes>::LexemeT, #actionskind #type_generics>>,
                    #parse_paramdef
                ) -> #actionskind #type_generics
                #where_clause
                {
                    #wrapper_fn_body
                }
             })
        }
        let mut actionskindvariants = Vec::new();
        let actionskindhidden = format_ident!("_{}", ACTIONS_KIND_HIDDEN);
        let actionskind = str::parse::<TokenStream>(ACTIONS_KIND).unwrap();
        let mut phantom_data_type = Vec::new();
        for ridx in grm.iter_rules() {
            if let Some(actiont) = grm.actiontype(ridx) {
                let actionskindvariant =
                    format_ident!("{}{}", ACTIONS_KIND_PREFIX, usize::from(ridx));
                let actiont = str::parse::<TokenStream>(actiont).unwrap();
                actionskindvariants.push(quote! {
                    #actionskindvariant(#actiont)
                })
            }
        }
        for lifetime in parsed_parse_generics.lifetimes() {
            let lifetime = &lifetime.lifetime;
            phantom_data_type.push(quote! { &#lifetime () });
        }
        for type_param in parsed_parse_generics.type_params() {
            let ident = &type_param.ident;
            phantom_data_type.push(quote! { #ident });
        }
        actionskindvariants.push(quote! {
            #actionskindhidden(::std::marker::PhantomData<(#(#phantom_data_type,)*)>)
        });
        wrappers.extend(quote! {
            #[allow(dead_code)]
            enum #actionskind #generics #where_clause {
                #(#actionskindvariants,)*
            }
        });
        Ok(wrappers)
    }

    /// Return the `RIdx` of the %start rule in the grammar (which will not be the same as
    /// grm.start_rule_idx because the latter has an additional rule insert by cfgrammar
    /// which then calls the user's %start rule).
    fn user_start_ridx(&self) -> RIdx<LexerTypesT::StorageT> {
        let grm = self.grm();
        debug_assert_eq!(grm.prod(grm.start_prod()).len(), 1);
        match grm.prod(grm.start_prod())[0] {
            Symbol::Rule(ridx) => ridx,
            _ => unreachable!(),
        }
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

/// The quote impl of `ToTokens` for `usize` prints literal values
/// including a type suffix for example `0usize`.
///
/// This wrapper omits the type suffix emitting `0` instead.
struct UnsuffixedUsize(usize);

impl ToTokens for UnsuffixedUsize {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        tokens.append(Literal::usize_unsuffixed(self.0))
    }
}

impl RustEdition {
    fn to_variant_tokens(self) -> TokenStream {
        match self {
            RustEdition::Rust2015 => quote!(::lrpar::RustEdition::Rust2015),
            RustEdition::Rust2018 => quote!(::lrpar::RustEdition::Rust2018),
            RustEdition::Rust2021 => quote!(::lrpar::RustEdition::Rust2021),
        }
    }
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

impl Visibility {
    fn to_variant_tokens(&self) -> TokenStream {
        match self {
            Visibility::Private => quote!(::lrpar::Visibility::Private),
            Visibility::Public => quote!(::lrpar::Visibility::Public),
            Visibility::PublicSuper => quote!(::lrpar::Visibility::PublicSuper),
            Visibility::PublicSelf => quote!(::lrpar::Visibility::PublicSelf),
            Visibility::PublicCrate => quote!(::lrpar::Visibility::PublicCrate),
            Visibility::PublicIn(data) => {
                let data = QuoteToString(data);
                quote!(::lrpar::Visibility::PublicIn(#data))
            }
        }
    }
}

impl ToTokens for SerialisationFormat {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        tokens.extend(match self {
            SerialisationFormat::FixedSizeInteger => {
                quote! {::lrpar::ctbuilder::SerialisationFormat::FixedSizeInteger}
            }
            SerialisationFormat::VariableSizedInteger => {
                quote! {::lrpar::ctbuilder::SerialisationFormat::VariableSizedInteger}
            }
        })
    }
}

pub(crate) fn make_generics(parse_generics: Option<&str>) -> Result<Generics, CodegenError> {
    if let Some(parse_generics) = parse_generics {
        let tokens = str::parse::<TokenStream>(parse_generics)?;
        match syn::parse2(quote!(<'lexer, 'input: 'lexer, #tokens>)) {
            Ok(res) => Ok(res),
            Err(err) => Err(CodegenError::InvalidParseGenerics(err)),
        }
    } else {
        Ok(parse_quote!(<'lexer, 'input: 'lexer>))
    }
}

#[cfg(test)]
mod test {
    use crate::test_utils::TestLexerTypes;
    use cfgrammar::{header::Header, span::Location};

    use super::*;
    #[test]
    fn test_unused_crate_header_entry() {
        let src = r#"
        %grmtools{
            yacckind: Grmtools,
            test.foo: "test crate value",
        }
        %%
        start -> () : "A" { () };
        "#;
        let empty_header = Header::<Location>::new();
        let src_env = ParserSrcEnv::<TestLexerTypes>::new_with_header(src, None, empty_header);
        let build_env = src_env
            .build_env(ParserBuildEnvArgs::new().mod_name(Some("test_module")))
            .unwrap();
        assert!(
            build_env
                .ast_with_validity_info()
                .unused_header_keys_for_crate(Some("cfgrammar"))
                .is_empty()
        );
        build_env
            .check_unused_header_keys_for_crate(Some("cfgrammar"))
            .unwrap();
        build_env
            .check_unused_header_keys_for_crate(Some("lrpar"))
            .unwrap();
        assert!(
            build_env
                .ast_with_validity_info()
                .unused_header_keys_for_crate(Some("lrpar"))
                .is_empty()
        );
        build_env
            .check_unused_header_keys_for_crate(Some("lrlex"))
            .unwrap();
        assert!(
            build_env
                .ast_with_validity_info()
                .unused_header_keys_for_crate(Some("lrpar"))
                .is_empty()
        );
        build_env.check_unused_header_keys_for_crate(None).unwrap();
        let codegen = build_env.code_generator("timestamp").unwrap();
        let out = codegen.generate(&build_env).unwrap();
        assert!(!out.is_empty());
    }

    #[test]
    fn test_unused_header_entry() {
        let src = r#"
        %grmtools{
            yacckind: Grmtools,
            testfoo: "values which do not specify a crate origin should show up as unused",
        }
        %%
        start -> () : "A" { () };
        "#;
        let empty_header = Header::<Location>::new();
        let src_env = ParserSrcEnv::<TestLexerTypes>::new_with_header(src, None, empty_header);
        let build_env = src_env
            .build_env(ParserBuildEnvArgs::new().mod_name(Some("test_module")))
            .unwrap();
        build_env
            .check_unused_header_keys_for_crate(Some("cfgrammar"))
            .unwrap();
        assert!(
            build_env
                .ast_with_validity_info()
                .unused_header_keys_for_crate(Some("cfgrammar"))
                .is_empty()
        );
        build_env
            .check_unused_header_keys_for_crate(Some("lrpar"))
            .unwrap();
        assert!(
            build_env
                .ast_with_validity_info()
                .unused_header_keys_for_crate(Some("lrpar"))
                .is_empty()
        );
        build_env
            .check_unused_header_keys_for_crate(Some("lrlex"))
            .unwrap();
        assert!(
            build_env
                .ast_with_validity_info()
                .unused_header_keys_for_crate(Some("lrlex"))
                .is_empty()
        );
        match build_env.check_unused_header_keys_for_crate(None) {
            Err(ParserBuildEnvError::GrmtoolsSectionUnusedKeys(keys))
                if keys == vec!["testfoo".to_string()] => {}
            _ => panic!("Unexpected return value for unused header keys check"),
        }
        let codegen = build_env.code_generator("timestamp").unwrap();
        let out = codegen.generate(&build_env).unwrap();
        assert!(!out.is_empty());
    }

    #[test]
    fn test_unused_grmtools_header_entry() {
        let src = r#"
        %grmtools{
            yacckind: Grmtools,
            cfgrammar.unknown: "should be unused",
            lrpar.unknown: "should be unused",
        }
        %%
        start -> () : "A" { () };
        "#;
        let empty_header = Header::<Location>::new();
        let src_env = ParserSrcEnv::<TestLexerTypes>::new_with_header(src, None, empty_header);
        let build_env = src_env
            .build_env(ParserBuildEnvArgs::new().mod_name(Some("test_module")))
            .unwrap();
        assert!(
            build_env
                .check_unused_header_keys_for_crate(Some("cfgrammar"))
                .is_err()
        );
        assert_eq!(
            build_env
                .ast_with_validity_info()
                .unused_header_keys_for_crate(Some("cfgrammar")),
            vec![(
                "cfgrammar.unknown".to_string(),
                src.find_span("cfgrammar.unknown")
            )]
        );
        assert!(
            build_env
                .check_unused_header_keys_for_crate(Some("lrpar"))
                .is_err()
        );
        assert_eq!(
            build_env
                .ast_with_validity_info()
                .unused_header_keys_for_crate(Some("lrpar")),
            vec![("lrpar.unknown".to_string(), src.find_span("lrpar.unknown"))]
        );
        build_env
            .check_unused_header_keys_for_crate(Some("lrlex"))
            .unwrap();
        assert!(
            build_env
                .ast_with_validity_info()
                .unused_header_keys_for_crate(Some("lrlex"))
                .is_empty()
        );
        let codegen = build_env.code_generator("timestamp").unwrap();
        let out = codegen.generate(&build_env).unwrap();
        assert!(!out.is_empty());
    }

    trait FindSpan {
        fn find_span(&self, s: &str) -> Span;
    }

    impl FindSpan for &'_ str {
        #[track_caller]
        fn find_span(&self, s: &str) -> Span {
            let start_pos = self.find(s).unwrap();
            Span::new(start_pos, start_pos + s.len())
        }
    }
}
