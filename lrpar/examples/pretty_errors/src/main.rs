use ariadne::{Label, Report, ReportKind, Source};
use cfgrammar::analysis::{Analysis, YaccGrammarWarningAnalysis};
use cfgrammar::yacc::ast::GrammarAST;
use cfgrammar::yacc::YaccKind;
use cfgrammar::{yacc::parser::SpansKind, Spanned};
use lrlex::{CTLexerBuilder, DefaultLexeme};
use lrpar::CTParserBuilder;
use std::ops::Range;
use std::process::ExitCode;

use cfgrammar::yacc::YaccGrammar;
const LEX_FILENAME: &str = "erroneous.l";
const YACC_FILENAME: &str = "erroneous.y";

pub struct EmptyAnalysis;

// We don't currently support anything for conflicts because they aren't spanned.
impl<T> Analysis<T> for EmptyAnalysis {
    fn analyse(&mut self, _: &T) {}
}

fn spanned_report<'a, T: Spanned>(
    w: &T,
    kind: ReportKind,
    file_name: &'a str,
    src: &str,
) -> Report<(&'a str, Range<usize>)> {
    let spans = w.spans();
    let span = spans.first().unwrap();
    // Character index seems to be relative to 0 rather than the
    // offset parameter of Report::build, or beginning of line?
    let span_prefix = &src[..span.start()];
    let span_prefix_len = span_prefix.chars().count();
    let span_substr_len = src[span.start()..span.end()].chars().count();
    let mut rb = Report::build(kind, file_name, span_prefix_len).with_label(
        Label::new((
            YACC_FILENAME,
            span_prefix_len..span_prefix_len + span_substr_len,
        ))
        .with_message(format!("{}", w)),
    );
    for span in spans.iter().skip(1) {
        let msg = match w.spanskind() {
            SpansKind::DuplicationError => Some("Duplicate"),
            SpansKind::Error => None,
        };
        let span_prefix = &src[..span.start()];
        let span_prefix_len = span_prefix.chars().count();
        let span_substr_len = src[span.start()..span.end()].chars().count();
        let label = Label::new((
            YACC_FILENAME,
            span_prefix_len..span_prefix_len + span_substr_len,
        ));
        let label = if let Some(msg) = msg {
            label.with_message(msg)
        } else {
            label
        };
        rb.add_label(label);
    }
    rb.finish()
}

pub struct AriadneYaccWarningAnalysis<SourceId>
where
    SourceId: PartialEq + ToOwned + ?Sized + Clone,
{
    pub warning_analysis: YaccGrammarWarningAnalysis<SourceId>,
}

impl AriadneYaccWarningAnalysis<String> {
    pub fn new(src_id: String) -> Self {
        Self {
            warning_analysis: YaccGrammarWarningAnalysis::new(&src_id),
        }
    }
    pub fn source_id(&self) -> &str {
        self.warning_analysis.source_id().as_ref()
    }

    #[allow(clippy::type_complexity)]
    pub fn reports(&self, src: &str) -> Option<Vec<Report<(&str, Range<usize>)>>> {
        let warnings = &self.warning_analysis;
        let mut reports = Vec::new();
        if !warnings.is_empty() {
            for warning in warnings.iter() {
                reports.push(spanned_report(
                    warning,
                    ReportKind::Warning,
                    self.source_id(),
                    src,
                ))
            }
            Some(reports)
        } else {
            None
        }
    }
}

impl Analysis<GrammarAST> for AriadneYaccWarningAnalysis<String> {
    fn analyse(&mut self, ast: &GrammarAST) {
        self.warning_analysis.analyse(ast)
    }
}

struct RailroadDiagramAnalysis {
    svg: String,
}

impl RailroadDiagramAnalysis {
    fn new() -> Self {
        Self {
            svg: String::new(),
        }
    }
}

impl Analysis<YaccGrammar> for RailroadDiagramAnalysis {
    /// The diagram this produces was a quick effort and could use some improvement.
    fn analyse(&mut self, grm: &YaccGrammar) {
        let mut node_idxs = std::collections::HashMap::new();
        let mut sequences: Vec<railroad::Sequence> = Vec::new();
        for (i, ridx) in grm.iter_rules().enumerate() {
            let name = grm.rule_name_str(ridx);
            let symbol = cfgrammar::Symbol::Rule(ridx);
            node_idxs.insert(symbol, i);
            sequences.push(railroad::Sequence::new(vec![Box::new(
                railroad::Comment::new(name.to_string()),
            )]));
        }

        for (i, tidx) in grm.iter_tidxs().enumerate() {
            let symbol = cfgrammar::Symbol::Token(tidx);
            node_idxs.insert(symbol, i);
        }

        for ridx in grm.iter_rules() {
            let prods = grm.rule_to_prods(ridx);
            let prod_syms = prods.iter().map(|pidx| grm.prod(*pidx)).collect::<Vec<_>>();
            let seq = sequences
                .get_mut(*node_idxs.get(&cfgrammar::Symbol::Rule(ridx)).unwrap())
                .unwrap();

            let mut choice = railroad::Choice::new(vec![]);
            for symbols in prod_syms {
                let mut a_seq = railroad::Sequence::new(vec![]);
                if !symbols.is_empty() {
                    for symbol in symbols {
                        match symbol {
                            cfgrammar::Symbol::Rule(prod_ridx) if prod_ridx == &ridx => {
                                let epsilon = grm.firsts().is_epsilon_set(ridx);
                                if epsilon {
                                    a_seq.push(Box::new(railroad::Repeat::new(
                                        Box::new(railroad::Empty),
                                        Box::new(railroad::NonTerminal::new(
                                            grm.rule_name_str(*prod_ridx).to_string(),
                                        )),
                                    )));
                                } else {
                                    a_seq.push(Box::new(railroad::Repeat::new(
                                        Box::new(railroad::NonTerminal::new(
                                            grm.rule_name_str(*prod_ridx).to_string(),
                                        )),
                                        Box::new(railroad::Empty),
                                    )));
                                }
                            }
                            cfgrammar::Symbol::Rule(prod_ridx) => {
                                a_seq.push(Box::new(railroad::NonTerminal::new(
                                    grm.rule_name_str(*prod_ridx).to_string(),
                                )));
                            }
                            cfgrammar::Symbol::Token(tidx) => {
                                a_seq.push(Box::new(railroad::Terminal::new(
                                    grm.token_name(*tidx).unwrap_or("anonymous").to_string(),
                                )));
                            }
                        }
                    }
                }
                choice.push(a_seq);
            }
            seq.push(Box::new(choice));
        }
        let mut vert = railroad::VerticalGrid::new(vec![]);
        for i in sequences {
            vert.push(Box::new(i));
        }
        let mut dia = railroad::Diagram::new(vert);
        dia.add_element(
            railroad::svg::Element::new("style")
                .set("type", "text/css")
                .raw_text(railroad::DEFAULT_CSS),
        );
        self.svg = format!("<html>{dia}</html>");
    }
}

fn main() -> ExitCode {
    eprintln!("{}", std::env::current_dir().unwrap().display());
    // We don't currently do anything fancy with `lex` errors.
    CTLexerBuilder::new()
        // This is a workaround for not running in build.rs
        // you should use `lexer_in_src_dir()` and `output_path` in a real build.rs.
        .lexer_path(format!("src/{}", LEX_FILENAME))
        .output_path("src/erroneous_l.rs")
        .build()
        .unwrap();

    let mut yacc_src_buf = String::new();
    let mut analysis = AriadneYaccWarningAnalysis::<String>::new(YACC_FILENAME.to_string());
    let mut railroad_analysis = RailroadDiagramAnalysis::new();
    let result = CTParserBuilder::<DefaultLexeme, u32>::new()
        .yacckind(YaccKind::Grmtools)
        // This is a workaround for not running within in build.rs
        // you should use `grammar_in_src_dir()` and `output_path`.
        .grammar_path(format!("src/{}", analysis.source_id()))
        .output_path("src/erroneous_y.rs")
        .build_for_analysis()
        .read_grammar(&mut yacc_src_buf)
        .unwrap()
        .build_ast(&yacc_src_buf)
        .analyse_ast(&mut analysis)
        .analyse_ast(&mut EmptyAnalysis)
        .build_grammar();

    match result {
        Ok(analyser) => {
            if analysis.warning_analysis.is_empty() {
                analyser
                    .analyse_grammar(&mut railroad_analysis)
                    .analyse_grammar(&mut EmptyAnalysis)
                    .build_table()
                    .unwrap()
                    .analyse_table(&mut EmptyAnalysis)
                    .analyse_table(&mut EmptyAnalysis)
                    .source_generator()
                    .write_parser()
                    .unwrap();
            } else {
                // Here if running under build.rs/cargo you should use `write` instead of `eprint`
                // then emit a [cargo:warning](https://doc.rust-lang.org/cargo/reference/build-scripts.html#cargo-warning).
                // Otherwise cargo won't actually display the warning, lacking any error.
                let _ = analysis
                    .reports(&yacc_src_buf)
                    .unwrap()
                    .iter()
                    .map(|r| {
                        r.eprint((analysis.source_id(), Source::from(&yacc_src_buf)))
                            .unwrap()
                    })
                    .collect::<()>();
            }
            println!("{}", railroad_analysis.svg);
            ExitCode::SUCCESS
        }
        Err(es) => {
            for e in es {
                spanned_report(&e, ReportKind::Error, analysis.source_id(), &yacc_src_buf)
                    .eprint((analysis.source_id(), Source::from(&yacc_src_buf)))
                    .unwrap();
            }
            analysis
                .reports(&yacc_src_buf)
                .unwrap()
                .iter()
                .for_each(|r| {
                    r.eprint((analysis.source_id(), Source::from(&yacc_src_buf)))
                        .unwrap()
                });
            ExitCode::FAILURE
        }
    }
}
