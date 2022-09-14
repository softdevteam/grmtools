use ariadne::{Label, Report, ReportKind, Source};
use cfgrammar::analysis::{Analysis, YaccGrammarWarningAnalysis};
use cfgrammar::yacc::ast::GrammarAST;
use cfgrammar::yacc::YaccKind;
use cfgrammar::{yacc::parser::SpansKind, Spanned};
use lrlex::{CTLexerBuilder, DefaultLexeme};
use lrpar::CTParserBuilder;
use std::ops::Range;
use std::process::ExitCode;

const LEX_FILENAME: &str = "erroneous.l";
const YACC_FILENAME: &str = "erroneous.y";

pub struct EmptyAnalysis;

// We don't currently support anything for conflicts because they aren't spanned.
impl<T> Analysis<T> for EmptyAnalysis {
    fn analyze(&mut self, _: &T) {}
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
    fn analyze(&mut self, ast: &GrammarAST) {
        self.warning_analysis.analyze(ast)
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
        .analyze_ast(&mut analysis)
        .analyze_ast(&mut EmptyAnalysis)
        .build_grammar();

    match result {
        Ok(analyzer) => {
            if analysis.warning_analysis.is_empty() {
                analyzer
                    .analyze_grammar(&mut EmptyAnalysis)
                    .analyze_grammar(&mut EmptyAnalysis)
                    .build_table()
                    .unwrap()
                    .analyze_table(&mut EmptyAnalysis)
                    .analyze_table(&mut EmptyAnalysis)
                    .source_generator()
                    .write_parser()
                    .unwrap();
            } else {
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
