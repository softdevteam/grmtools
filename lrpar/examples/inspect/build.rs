#![deny(rust_2018_idioms)]
use cfgrammar::{yacc::YaccGrammar, Span};
use lrlex::{CTLexerBuilder, DefaultLexerTypes, LRNonStreamingLexerDef, LexerDef};
use lrpar::{LexerTypes, RTParserBuilder};
use num_traits::ToPrimitive as _;
use std::io::Read;

pub fn set_rule_ids<LexerTypesT: LexerTypes<StorageT = u32>, LT: LexerDef<LexerTypesT>>(
    lexerdef: &mut LT,
    grm: &YaccGrammar,
) -> (Option<Vec<Span>>, Option<Vec<Span>>)
where
    usize: num_traits::AsPrimitive<LexerTypesT::StorageT>,
{
    let rule_ids = grm
        .tokens_map()
        .iter()
        .map(|(&n, &i)| (n, usize::from(i).to_u32().unwrap()))
        .collect::<std::collections::HashMap<&str, u32>>();
    let (missing_from_lexer, missing_from_parser) = lexerdef.set_rule_ids_spanned(&rule_ids);
    let missing_from_lexer = missing_from_lexer.map(|tokens| {
        tokens
            .iter()
            .map(|name| {
                grm.token_span(*grm.tokens_map().get(name).unwrap())
                    .expect("Given token should have a span")
            })
            .collect::<Vec<_>>()
    });

    let missing_from_parser =
        missing_from_parser.map(|tokens| tokens.iter().map(|(_, span)| *span).collect::<Vec<_>>());
    (missing_from_lexer, missing_from_parser)
}

fn main() {
    // Since we're using both lrlex and lrpar, we use lrlex's `lrpar_config` convenience function
    // that makes it easy to a) create a lexer and parser and b) link them together.
    CTLexerBuilder::new()
        .rust_edition(lrlex::RustEdition::Rust2021)
        .lrpar_config(|ctp| {
            ctp.rust_edition(lrpar::RustEdition::Rust2021)
                .inspect(Box::new(move |_, recov, grm, stable, _, lexer_path| {
                    let good_srcs = ["", "TODO: [Walk, relax]", "todo: [run, rest]"];
                    let bad_srcs = [
                        // Should start with TODO:
                        "Frodo: [Breakfast, Elevenses]",
                    ];
                    let mut lexer_src = String::new();
                    let _ = std::fs::File::open(lexer_path.unwrap())
                        .unwrap()
                        .read_to_string(&mut lexer_src);
                    let mut lexerdef =
                        LRNonStreamingLexerDef::<DefaultLexerTypes>::from_str(&lexer_src).unwrap();
                    set_rule_ids(&mut lexerdef, grm);
                    let pb = RTParserBuilder::new(grm, stable).recoverer(recov);
                    for src in good_srcs {
                        let lexer = lexerdef.lexer(src);
                        let errs = pb.parse_noaction(&lexer);
                        if !errs.is_empty() {
                            return Err(format!("{:?} while parsing src: {}", errs, src).into());
                        }
                    }
                    for src in bad_srcs {
                        let lexer = lexerdef.lexer(src);
                        let errs = pb.parse_noaction(&lexer);
                        if errs.is_empty() {
                            return Err(format!(
                                "Parse of source '{src}' succeeded while expecting failure"
                            )
                            .into());
                        }
                    }
                    Ok(())
                }))
                .grammar_in_src_dir("todo.y")
                .unwrap()
        })
        .lexer_in_src_dir("todo.l")
        .unwrap()
        .build()
        .unwrap();
}
