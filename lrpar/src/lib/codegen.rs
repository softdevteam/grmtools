#![deny(unfulfilled_lint_expectations)]
#![expect(dead_code)]

use crate::{
    LexerTypes, RecoveryKind, RustEdition, SerialisationFormat, Visibility,
    ctbuilder::ERROR,
    diagnostics::{DiagnosticFormatter, SpannedDiagnosticFormatter},
};
use cfgrammar::{
    Location, RIdx, Span, Symbol,
    header::{GrmtoolsSectionParser, Header, HeaderValue},
    yacc::{YaccGrammar, YaccKind, YaccOriginalActionKind, ast::ASTWithValidityInfo},
};
use lrtable::{Minimiser, StateGraph, StateTable, from_yacc};
use proc_macro2::{Literal, TokenStream};
use quote::{ToTokens, TokenStreamExt, format_ident, quote};
use std::{
    any::type_name,
    error::Error,
    fmt::{self, Debug, Write},
    hash::Hash,
    marker::PhantomData,
    path::Path,
};
use syn::{Generics, parse_quote};

use wincode::SchemaWrite;

const ACTION_PREFIX: &str = "__gt_";
const GLOBAL_PREFIX: &str = "__GT_";
const ACTIONS_KIND: &str = "__GtActionsKind";
const ACTIONS_KIND_PREFIX: &str = "Ak";
const ACTIONS_KIND_HIDDEN: &str = "__GtActionsKindHidden";

/// Defaults to `wincode::int_encoding::VarInt`.
type FixIntConfig = wincode::config::Configuration;
/// The default config with the last parameter set to `VarInt`
type VarIntConfig = wincode::config::Configuration<
    true,
    4194304,
    wincode::len::BincodeLen,
    wincode::int_encoding::LittleEndian,
    wincode::int_encoding::VarInt,
>;

pub(crate) struct ParserSrcEnv<'a> {
    src: &'a str,
    // We store the path here so we can generate a module name from it if needed.
    // But should never use it for filesystem interaction within this module.
    path: &'a Path,
    diagnostics: SpannedDiagnosticFormatter<'a>,
    header: Header<Location>,
}

pub(crate) struct ParserBuildEnvArgs<'a> {
    /// This allows the parser to originate from from a pre-parsed AST, rather than
    /// parsing a grammar definition given as source string into an AST.
    ast_originated: Option<&'a ASTWithValidityInfo>,
    mod_name: Option<String>,
    rust_edition: RustEdition,
    visibility: Visibility,
    error_on_conflicts: bool,
    show_warnings: bool,
    warnings_are_errors: bool,
}

impl<'a> ParserBuildEnvArgs<'a> {
    pub(crate) fn new() -> Self {
        ParserBuildEnvArgs {
            ast_originated: None,
            mod_name: None,
            visibility: Visibility::Private,
            rust_edition: RustEdition::Rust2021,
            error_on_conflicts: true,
            show_warnings: true,
            warnings_are_errors: true,
        }
    }

    pub(crate) fn ast_originated(mut self, ast: Option<&'a ASTWithValidityInfo>) -> Self {
        self.ast_originated = ast;
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

pub(crate) struct ParserBuildEnv<'a, LexerTypesT>
where
    LexerTypesT: LexerTypes,
    usize: num_traits::AsPrimitive<LexerTypesT::StorageT>,
{
    ast_validation: ASTWithValidityInfo,
    pub(crate) recoverer: RecoveryKind,
    serialisation_format: SerialisationFormat,
    // Preserve the args for generating the cache.
    cache_args: ParserBuildEnvArgs<'a>,
    phantom_storaget: PhantomData<LexerTypesT::StorageT>,
    mod_name: String,
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

impl<'a> ParserSrcEnv<'a> {
    pub(crate) fn new_with_defaults(
        src: &'a str,
        path: &'a Path,
        header: Header<Location>,
    ) -> ParserSrcEnv<'a> {
        let diagnostics = SpannedDiagnosticFormatter::new(src, path);
        ParserSrcEnv {
            src,
            path,
            header,
            diagnostics,
        }
    }

    pub(crate) fn yacc_diag(&self) -> &SpannedDiagnosticFormatter<'a> {
        &self.diagnostics
    }

    pub(crate) fn header_mut(&mut self) -> &mut Header<Location> {
        &mut self.header
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
                    self.yacc_diag()
                        .file_location_msg(" parsing the `%grmtools` section", None)
                ));
                for e in es {
                    out.push_str(&indent(
                        "     ",
                        &self.yacc_diag().format_error(e).to_string(),
                    ));
                    out.push('\n');
                }
                ErrorString(out).into()
            })
    }

    pub(crate) fn check_unused_header_keys(&self) -> Result<(), Box<dyn Error>> {
        let unused_keys = self.header.unused();
        if !unused_keys.is_empty() {
            return Err(format!("Unused keys in header: {}", unused_keys.join(", ")).into());
        }
        let missing_keys = self
            .header
            .missing()
            .iter()
            .map(|s| s.as_str())
            .collect::<Vec<_>>();
        if !missing_keys.is_empty() {
            Err(format!(
                "Required values were missing from the header: {}",
                missing_keys.join(", ")
            )
            .into())
        } else {
            Ok(())
        }
    }

    pub(crate) fn extract_ast_validation(
        &mut self,
        from_ast: Option<&ASTWithValidityInfo>,
    ) -> Result<ASTWithValidityInfo, Box<dyn Error>> {
        self.header.mark_used(&"yacckind".to_string());
        if let Some(ast) = from_ast {
            Ok(ast.clone())
        } else if let Some(yk) = self
            .header
            .get("yacckind")
            .map(|HeaderValue(_, val)| val)
            .map(YaccKind::try_from)
            .transpose()?
        {
            Ok(ASTWithValidityInfo::new(yk, self.src))
        } else {
            Err("Missing 'yacckind'".to_string())?
        }
    }

    pub(crate) fn extract_recoverer(&mut self) -> Result<RecoveryKind, Box<dyn Error>> {
        self.header.mark_used(&"recoverer".to_string());
        let rk_val = self
            .header
            .get("recoverer")
            .map(|HeaderValue(_, rk_val)| rk_val);
        if let Some(rk_val) = rk_val {
            Ok(RecoveryKind::try_from(rk_val)?)
        } else {
            // Fallback to the default recoverykind.
            Ok(RecoveryKind::CPCTPlus)
        }
    }

    pub(crate) fn extract_serialisation_format(
        &mut self,
    ) -> Result<SerialisationFormat, Box<dyn Error>> {
        self.header.mark_used(&"serialisation_format".to_string());
        if let Some(ec_val) = self
            .header
            .get("serialisation_format")
            .map(|HeaderValue(_, ec_val)| ec_val)
        {
            Ok(SerialisationFormat::try_from(ec_val)?)
        } else {
            Ok(SerialisationFormat::VariableSizedInteger)
        }
    }

    pub(crate) fn extract_mod_name(&self, args: &ParserBuildEnvArgs) -> String {
        match &args.mod_name {
            Some(s) => s.to_owned(),
            None => {
                // The user hasn't specified a module name, so we create one automatically: what we
                // do is strip off all the filename extensions (note that it's likely that inp ends
                // with `y.rs`, so we potentially have to strip off more than one extension) and
                // then add `_y` to the end.
                let mut stem = self.path.to_str().unwrap();
                loop {
                    let new_stem = Path::new(stem).file_stem().unwrap().to_str().unwrap();
                    if stem == new_stem {
                        break;
                    }
                    stem = new_stem;
                }
                format!("{}_y", stem)
            }
        }
    }

    pub(crate) fn build_env<LexerTypesT>(
        &mut self,
        args: ParserBuildEnvArgs<'a>,
    ) -> Result<ParserBuildEnv<'a, LexerTypesT>, Box<dyn Error>>
    where
        LexerTypesT: LexerTypes,
        usize: num_traits::AsPrimitive<LexerTypesT::StorageT>,
    {
        self.merge_headers()?;
        let ast_validation = self.extract_ast_validation(args.ast_originated)?;
        let recoverer = self.extract_recoverer()?;
        let serialisation_format = self.extract_serialisation_format()?;
        let mod_name = self.extract_mod_name(&args);

        Ok(ParserBuildEnv {
            ast_validation,
            cache_args: args,
            recoverer,
            serialisation_format,
            mod_name,
            phantom_storaget: PhantomData,
        })
    }
}

impl<'a, LexerTypesT> ParserBuildEnv<'a, LexerTypesT>
where
    LexerTypesT: LexerTypes,
    usize: num_traits::AsPrimitive<LexerTypesT::StorageT>,
{
    pub(crate) fn ast_validation(&self) -> &ASTWithValidityInfo {
        &self.ast_validation
    }

    pub(crate) fn code_generator(
        &self,
        src_env: &ParserSrcEnv,
        timestamp: &str,
    ) -> Result<ParserCodegen<LexerTypesT>, Box<dyn Error>> {
        let grm = match YaccGrammar::<LexerTypesT::StorageT>::new_from_ast_with_validity_info(
            &self.ast_validation,
        ) {
            Ok(grm) => grm,
            Err(errs) => {
                let mut out = String::new();
                out.push_str(&format!(
                    "\n{ERROR}{}\n",
                    src_env.yacc_diag().file_location_msg("", None)
                ));
                for e in errs {
                    out.push_str(&indent(
                        "     ",
                        &src_env.yacc_diag().format_error(e).to_string(),
                    ));
                    out.push('\n');
                }
                return Err(ErrorString(out).into());
            }
        };

        let (sgraph, stable) = from_yacc(&grm, Minimiser::Pager)?;
        if self.cache_args.error_on_conflicts
            && let Some(c) = stable.conflicts()
        {
            match (grm.expect(), grm.expectrr()) {
                (Some(i), Some(j)) if i == c.sr_len() && j == c.rr_len() => (),
                (Some(i), None) if i == c.sr_len() && 0 == c.rr_len() => (),
                (None, Some(j)) if 0 == c.sr_len() && j == c.rr_len() => (),
                (None, None) if 0 == c.rr_len() && 0 == c.sr_len() => (),
                _ => {
                    let conflicts_diagnostic = src_env.yacc_diag().format_conflicts::<LexerTypesT>(
                        &grm,
                        self.ast_validation.ast(),
                        c,
                        &sgraph,
                        &stable,
                    );
                    return Err(Box::new(CTConflictsError {
                        conflicts_diagnostic,
                        phantom: PhantomData,
                        #[cfg(test)]
                        stable,
                    }));
                }
            }
        }

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

    pub(crate) fn generate(
        &self,
        src_env: &ParserSrcEnv,
        build_env: &ParserBuildEnv<LexerTypesT>,
    ) -> Result<String, Box<dyn Error>> {
        let grm = &self.grm;
        let stable = &self.stable;
        let visibility = build_env.cache_args.visibility.clone();
        let user_actions = if let YaccKind::Original(YaccOriginalActionKind::UserAction)
        | YaccKind::Grmtools = build_env.ast_validation().yacc_kind()
        {
            Some(self.gen_user_actions(&self.grm, src_env.yacc_diag())?)
        } else {
            None
        };
        let rule_consts = self.gen_rule_consts(grm)?;
        let token_epp = self.gen_token_epp(grm)?;
        let parse_function = self.gen_parse_function(build_env, src_env, grm, stable)?;
        let action_wrappers = match build_env.ast_validation().yacc_kind() {
            YaccKind::Original(YaccOriginalActionKind::UserAction) | YaccKind::Grmtools => {
                Some(self.gen_wrappers(build_env, src_env)?)
            }
            YaccKind::Original(YaccOriginalActionKind::NoAction)
            | YaccKind::Original(YaccOriginalActionKind::GenericParseTree) => None,
            _ => unreachable!(),
        };

        let additional_decls = if let YaccKind::Original(YaccOriginalActionKind::GenericParseTree) =
            build_env.ast_validation().yacc_kind()
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

        let mod_name =
            match syn::parse_str::<proc_macro2::Ident>(&build_env.mod_name) {
                Ok(s) => s,
                Err(e) => return Err(format!(
                    "CTParserBuilder::mod_name(\"{}\") is not a valid rust identifier due to '{}'",
                    build_env.mod_name, e
                )
                .into()),
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
        let outs = syn::parse_str(&unformatted)
            .map(|syntax_tree| prettyplease::unparse(&syntax_tree))
            .unwrap_or(unformatted);
        Ok(outs)
    }

    pub(crate) fn cache_string(
        &self,
        src_env: &ParserSrcEnv,
        build_env: &ParserBuildEnv<LexerTypesT>,
    ) -> String {
        self.gen_cache(src_env, build_env).to_string()
    }

    pub(crate) fn take_parser(
        self,
    ) -> (
        YaccGrammar<LexerTypesT::StorageT>,
        StateGraph<LexerTypesT::StorageT>,
        StateTable<LexerTypesT::StorageT>,
    ) {
        (self.grm, self.sgraph, self.stable)
    }

    /// Generate the cache, which determines if anything's changed enough that we need to
    /// regenerate outputs and force rustc to recompile.
    fn gen_cache(
        &self,
        src_env: &ParserSrcEnv,
        build_env: &ParserBuildEnv<LexerTypesT>,
    ) -> TokenStream {
        let build_time = &self.timestamp;
        let grammar_path = src_env.path.to_string_lossy();
        let mod_name = QuoteOption(build_env.cache_args.mod_name.as_deref());
        let visibility = build_env.cache_args.visibility.to_variant_tokens();
        let rust_edition = build_env.cache_args.rust_edition.to_variant_tokens();
        let yacckind = build_env.ast_validation().yacc_kind();
        let rule_map = self
            .grm
            .iter_tidxs()
            .map(|tidx| {
                QuoteTuple((
                    usize::from(tidx),
                    self.grm.token_name(tidx).unwrap_or("<unknown>"),
                ))
            })
            .collect::<Vec<_>>();
        let derived_mod_name = &build_env.mod_name;
        let serialisation_format = build_env.serialisation_format;
        let recoverer = build_env.recoverer;
        let error_on_conflicts = build_env.cache_args.error_on_conflicts;
        let show_warnings = build_env.cache_args.show_warnings;
        let warnings_are_errors = build_env.cache_args.warnings_are_errors;
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

    /// Generate the user action functions (if any).
    fn gen_user_actions(
        &self,
        grm: &YaccGrammar<LexerTypesT::StorageT>,
        diag: &SpannedDiagnosticFormatter,
    ) -> Result<TokenStream, Box<dyn Error>> {
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
                        if let Some(action_type) = grm.actiontype(ref_ridx).as_ref() {
                            str::parse::<TokenStream>(action_type)?
                        } else {
                            let mut s = String::from("\n");
                            let rule_span = grm.rule_name_span(ref_ridx);
                            s.push_str(&diag.file_location_msg("Error", Some(rule_span)));
                            s.push('\n');
                            s.push_str(&diag.underline_span_with_text(
                                rule_span,
                                "Rule missing action type".to_string(),
                                '^',
                            ));
                            return Err(ErrorString(s).into());
                        }
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
            let pre_action = grm.action(pidx).as_ref().ok_or_else(|| {
                let mut s = String::from("\n");
                let span = grm.prod_span(pidx);
                s.push_str(&diag.file_location_msg("Error", Some(span)));
                s.push('\n');
                s.push_str(&diag.underline_span_with_text(
                    span,
                    "Production is missing action code".to_string(),
                    '^',
                ));
                ErrorString(s)
            })?;
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
                            let span = grm.action_span(pidx).unwrap();
                            let inner_span =
                                Span::new(span.start() + last + off + "$".len(), span.end());
                            let mut s = String::from("\n");
                            s.push_str(&diag.file_location_msg("Error", Some(inner_span)));
                            s.push('\n');
                            s.push_str(&diag.underline_span_with_text(
                                inner_span,
                                "Unknown text following '$'".to_string(),
                                '^',
                            ));
                            return Err(ErrorString(s).into());
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

    fn gen_rule_consts(
        &self,
        grm: &YaccGrammar<LexerTypesT::StorageT>,
    ) -> Result<TokenStream, proc_macro2::LexError> {
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

    fn gen_token_epp(
        &self,
        grm: &YaccGrammar<LexerTypesT::StorageT>,
    ) -> Result<TokenStream, proc_macro2::LexError> {
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
        _src_env: &ParserSrcEnv,
        grm: &YaccGrammar<LexerTypesT::StorageT>,
        stable: &StateTable<LexerTypesT::StorageT>,
    ) -> Result<TokenStream, Box<dyn Error>> {
        let storaget = str::parse::<TokenStream>(type_name::<LexerTypesT::StorageT>())?;
        let lexertypest = str::parse::<TokenStream>(type_name::<LexerTypesT>())?;
        let recoverer = build_env.recoverer;
        let run_parser = match build_env.ast_validation().yacc_kind() {
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
                let edition_lifetime = if build_env.cache_args.rust_edition != RustEdition::Rust2015
                {
                    quote!('_,)
                } else {
                    quote!()
                };
                let ridx = usize::from(self.user_start_ridx(grm));
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

        let parsed_parse_generics: Generics = match build_env.ast_validation().yacc_kind() {
            YaccKind::Original(YaccOriginalActionKind::UserAction) | YaccKind::Grmtools => {
                make_generics(grm.parse_generics().as_deref())?
            }
            _ => make_generics(None)?,
        };
        let (generics, _, where_clause) = parsed_parse_generics.split_for_impl();

        // `parse()` may or may not have an argument for `%parseparam`.
        let parse_fn_parse_param = match build_env.ast_validation().yacc_kind() {
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
        let parse_fn_return_ty = match build_env.ast_validation().yacc_kind() {
            YaccKind::Original(YaccOriginalActionKind::UserAction) | YaccKind::Grmtools => {
                let actiont = grm
                    .actiontype(self.user_start_ridx(grm))
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

        let serialisation_format = build_env.serialisation_format;
        // Note that the configuration types use associated consts, and thus these configurations represent distinct types.
        let (grm_data, stable_data): (Vec<u8>, Vec<u8>) = match serialisation_format {
            SerialisationFormat::FixedSizeInteger => {
                let config = wincode::config::Configuration::default().with_fixint_encoding();
                let grm = wincode::config::serialize(&self.grm, config)?;
                let stable = wincode::config::serialize(stable, config)?;
                (grm, stable)
            }
            SerialisationFormat::VariableSizedInteger => {
                let config = wincode::config::Configuration::default().with_varint_encoding();
                let grm = wincode::config::serialize(&self.grm, config)?;
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
        _src_env: &ParserSrcEnv,
    ) -> Result<TokenStream, Box<dyn Error>> {
        let parsed_parse_generics = make_generics(self.grm.parse_generics().as_deref())?;
        let (generics, type_generics, where_clause) = parsed_parse_generics.split_for_impl();

        let (parse_paramname, parse_paramdef);
        match self.grm.parse_param() {
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
        for pidx in self.grm.iter_pidxs() {
            let ridx = self.grm.prod_to_rule(pidx);

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
            let edition_lifetime = if build_env.cache_args.rust_edition != RustEdition::Rust2015 {
                Some(quote!('_,))
            } else {
                None
            };
            let mut wrapper_fn_body = TokenStream::new();
            if self.grm.action(pidx).is_some() {
                // Unpack the arguments passed to us by the drain
                for i in 0..self.grm.prod(pidx).len() {
                    let arg = format_ident!("{}arg_{}", ACTION_PREFIX, i + 1);
                    wrapper_fn_body.extend(match self.grm.prod(pidx)[i] {
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
                let args = (0..self.grm.prod(pidx).len())
                    .map(|i| format_ident!("{}arg_{}", ACTION_PREFIX, i + 1))
                    .collect::<Vec<_>>();
                let action_fn = format_ident!("{}action_{}", ACTION_PREFIX, usize::from(pidx));
                let actionsvariant = format_ident!("{}{}", ACTIONS_KIND_PREFIX, usize::from(ridx));

                wrapper_fn_body.extend(match self.grm.actiontype(ridx) {
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
            } else if pidx == self.grm.start_prod() {
                wrapper_fn_body.extend(quote!(unreachable!()));
            } else {
                unreachable!(
                    "Production in rule '{}' must have an action body, which should have been handled by gen_user_actions.",
                    self.grm.rule_name_str(self.grm.prod_to_rule(pidx))
                );
            };

            let attrib = if pidx == self.grm.start_prod() {
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
        for ridx in self.grm.iter_rules() {
            if let Some(actiont) = self.grm.actiontype(ridx) {
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
    fn user_start_ridx(
        &self,
        grm: &YaccGrammar<LexerTypesT::StorageT>,
    ) -> RIdx<LexerTypesT::StorageT> {
        debug_assert_eq!(grm.prod(grm.start_prod()).len(), 1);
        match grm.prod(grm.start_prod())[0] {
            Symbol::Rule(ridx) => ridx,
            _ => unreachable!(),
        }
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

fn make_generics(parse_generics: Option<&str>) -> Result<Generics, Box<dyn Error>> {
    if let Some(parse_generics) = parse_generics {
        let tokens = str::parse::<TokenStream>(parse_generics)?;
        match syn::parse2(quote!(<'lexer, 'input: 'lexer, #tokens>)) {
            Ok(res) => Ok(res),
            Err(err) => Err(format!("unable to parse %parse-generics: {}", err).into()),
        }
    } else {
        Ok(parse_quote!(<'lexer, 'input: 'lexer>))
    }
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

/// This wrapper adds a missing impl of `ToTokens` for tuples.
/// For a tuple `(a, b)` emits `(a.to_tokens(), b.to_tokens())`
struct QuoteTuple<T>(T);

impl<A: ToTokens, B: ToTokens> ToTokens for QuoteTuple<(A, B)> {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let (a, b) = &self.0;
        tokens.append_all(quote!((#a, #b)));
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

impl RustEdition {
    fn to_variant_tokens(self) -> TokenStream {
        match self {
            RustEdition::Rust2015 => quote!(::lrpar::RustEdition::Rust2015),
            RustEdition::Rust2018 => quote!(::lrpar::RustEdition::Rust2018),
            RustEdition::Rust2021 => quote!(::lrpar::RustEdition::Rust2021),
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

pub(crate) struct CTConflictsError<StorageT: Eq + Hash> {
    pub(crate) conflicts_diagnostic: String,
    #[cfg(test)]
    #[cfg_attr(test, allow(dead_code))]
    pub(crate) stable: StateTable<StorageT>,
    pub(crate) phantom: PhantomData<StorageT>,
}

impl<StorageT> fmt::Display for CTConflictsError<StorageT>
where
    StorageT: 'static + Debug + Hash + num_traits::PrimInt + num_traits::Unsigned,
    usize: num_traits::AsPrimitive<StorageT>,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.conflicts_diagnostic)
    }
}

impl<StorageT> fmt::Debug for CTConflictsError<StorageT>
where
    StorageT: 'static + Debug + Hash + num_traits::PrimInt + num_traits::Unsigned,
    usize: num_traits::AsPrimitive<StorageT>,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.conflicts_diagnostic)
    }
}

impl<StorageT> Error for CTConflictsError<StorageT>
where
    StorageT: 'static + Debug + Hash + num_traits::PrimInt + num_traits::Unsigned,
    usize: num_traits::AsPrimitive<StorageT>,
{
}
