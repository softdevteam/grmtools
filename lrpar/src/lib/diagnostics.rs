use std::{cell::OnceCell, error::Error, fmt::Display, path::Path};

use crate::LexerTypes;
use cfgrammar::{
    PIdx, Span, Spanned,
    newlinecache::NewlineCache,
    yacc::{
        YaccGrammar,
        ast::{GrammarAST, Symbol},
        parser::SpansKind,
    },
};
use lrtable::statetable::Conflicts;
use unicode_width::UnicodeWidthStr;

pub struct SpannedDiagnosticFormatter<'a> {
    src: &'a str,
    path: &'a Path,
    nlc: OnceCell<NewlineCache>,
}

/// Implements a `pushln` convenience function to `String`
trait PushLine {
    /// Appends a given string slice and a newline to the end of this `String`.
    fn pushln<S: AsRef<str>>(&mut self, s: S);
}

impl PushLine for String {
    fn pushln<S: AsRef<str>>(&mut self, s: S) {
        self.push_str(s.as_ref());
        self.push('\n');
    }
}

fn pidx_prods_data<StorageT>(ast: &GrammarAST, pidx: PIdx<StorageT>) -> (Vec<String>, Vec<Span>)
where
    usize: num_traits::AsPrimitive<StorageT>,
    StorageT: 'static + num_traits::PrimInt + num_traits::Unsigned,
{
    let prod = &ast.prods[usize::from(pidx)];
    prod.symbols
        .iter()
        .map(|sym| match sym {
            Symbol::Rule(name, span) => (format!("'{}'", name), span),
            Symbol::Token(name, span) => (format!("'{}'", name), span),
        })
        .unzip()
}

impl<'a> SpannedDiagnosticFormatter<'a> {
    #[allow(clippy::result_unit_err)]
    pub fn new(src: &'a str, path: &'a Path) -> Self {
        Self {
            src,
            path,
            nlc: OnceCell::new(),
        }
    }

    pub fn nlc(&self) -> &NewlineCache {
        self.nlc.get_or_init(|| {
            let mut nlc = NewlineCache::new();
            nlc.feed(self.src);
            nlc
        })
    }

    pub fn ordinal(v: usize) -> String {
        // I didn't feel like thinking about these special cases,
        // so I just borrowed this from rusts diagnostics code.
        let suffix = match ((11..=13).contains(&(v % 100)), v % 10) {
            (false, 1) => "st",
            (false, 2) => "nd",
            (false, 3) => "rd",
            _ => "th",
        };
        format!("{v}{suffix}")
    }

    // If a span is given returns "msg at path/file.foo:5:6" otherwise returns "msg in path/file.foo"
    pub fn file_location_msg(&self, msg: &str, span: Option<Span>) -> String {
        if let Some(span) = span {
            let (line, col) = self
                .nlc()
                .byte_to_line_num_and_col_num(self.src, span.start())
                .unwrap_or((0, 0));
            format!("{} at {}:{line}:{col}", msg, self.path.display())
        } else {
            format!("{} in {}", msg, self.path.display())
        }
    }

    /// Print the line/column information and source text for all lines intersecting the span.
    /// Underline the portion covered by the span with the `underline_c` character.
    pub fn underline_span_with_text(&self, span: Span, s: String, underline_c: char) -> String {
        self.prefixed_underline_span_with_text("", span, s, underline_c)
    }

    // This prints a span with an optional prefix under the line numbers, which
    // is intended to be used for denoting when lines are non-contiguous.
    pub fn prefixed_underline_span_with_text(
        &self,
        prefix: &str,
        mut span: Span,
        s: String,
        underline_c: char,
    ) -> String {
        let mut out = String::new();
        let (start_byte, end_byte) = self.nlc().span_line_bytes(span);
        // Produce an underline underneath a span which may cover multiple lines, and a message on the last line.
        let mut source_lines = self.src[start_byte..end_byte].lines().peekable();
        while let Some(source_line) = source_lines.next() {
            let (line_start_byte, _) = self.nlc().span_line_bytes(span);
            let span_offset_from_start = span.start() - line_start_byte;

            // An underline bounded by the current line.
            let underline_span = Span::new(
                span.start(),
                span.end()
                    .min(span.start() + (source_line.len() - span_offset_from_start)),
            );
            let (line_num, _) = self
                .nlc()
                .byte_to_line_num_and_col_num(self.src, span.start())
                .expect("Span must correlate to a line in source");
            // Print the line_num/source text for the line.
            out.push_str(&format!("{}| {}\n", line_num, source_line));
            let line_num_digits = line_num.to_string().len();
            assert!(prefix.len() <= "0| ".len());
            // Add indentation from the start of the underlined span
            out.push_str(&format!(
                "{prefix}{}",
                &" ".repeat(
                    UnicodeWidthStr::width(&self.src[line_start_byte..underline_span.start()])
                        + (line_num_digits + "| ".len() - prefix.len())
                )
            ));
            // Add underline upto the end of line.
            out.push_str(
                &(underline_c.to_string()).repeat(
                    UnicodeWidthStr::width(&self.src[underline_span.start()..underline_span.end()])
                        .max(1),
                ),
            );

            if source_lines.peek().is_none() {
                // If we're at the end print the message.
                out.push_str(&format!(" {}", &s));
            } else {
                // Otherwise set next span to start at the beginning of the next line.
                out.push('\n');
                span = Span::new(line_start_byte + source_line.len() + 1, span.end())
            }
        }

        out
    }

    fn format_spanned(&self, e: &impl Spanned) -> String {
        let mut out = String::new();
        let mut spans = e.spans().iter().enumerate().peekable();
        while let Some((span_num, span)) = spans.next() {
            let (line, _) = self
                .nlc()
                .byte_to_line_num_and_col_num(self.src, span.start())
                .unwrap_or((0, 0));
            let next_line = spans
                .peek()
                .map(|(_, span)| span)
                .map(|s| self.nlc().byte_to_line_num(s.start()).unwrap_or(line))
                .unwrap_or(line);
            // Is this line contiguous with the next, if not prefix it with dots.
            let dots = if next_line - line > 1 { "..." } else { "" };
            if span_num == 0 {
                let s = e.to_string();
                out.push_str(&self.prefixed_underline_span_with_text(dots, *span, s, '^'));
            } else {
                out.push('\n');
                let s = match e.spanskind() {
                    SpansKind::DuplicationError => {
                        format!("{} occurrence", Self::ordinal(span_num + 1))
                    }
                    SpansKind::Error => {
                        unreachable!("Should contain a single span at the site of the error")
                    }
                    _ => "Unrecognized spanskind".to_string(),
                };
                out.push_str(&self.prefixed_underline_span_with_text(dots, *span, s, '^'));
            }
        }
        out
    }

    /// This function panics if the items in the `spans` iterator span more than a single line.
    ///
    /// This function only produces if all the following are true:
    /// 1. Spans are sorted in left-to-right order.
    /// 2. Spans are non-overlapping.
    fn underline_spans_on_line_with_text(
        &self,
        spans: impl Iterator<Item = Span> + Clone,
        msg: String,
        underline_c: char,
    ) -> String {
        let mut lines = spans
            .clone()
            .map(|span| self.nlc().span_line_bytes(span))
            .collect::<Vec<_>>();
        lines.dedup();
        assert!(lines.len() == 1);
        let mut spans = spans.peekable();
        let first_span = spans.peek().unwrap();
        let mut out = String::new();
        // For instance we want to underline the b's in
        // aaaaa bbbb cccc bbb
        //       ____      ___
        // indent    indent
        let (line_at_start, _) = self
            .nlc()
            .byte_to_line_num_and_col_num(self.src, first_span.start())
            .expect("Span should correlate to a line in source");
        let (line_start_byte, end_byte) = self.nlc().span_line_bytes(*first_span);
        // Print the line_num/source text for the line.
        out.push_str(&format!(
            "{}| {}\n",
            line_at_start,
            &self.src[line_start_byte..end_byte]
        ));
        // Indent from the beginning of the line up to span.start() of the first span.
        let line_num_digits = line_at_start.to_string().len();
        out.push_str(&" ".repeat(
            UnicodeWidthStr::width(&self.src[line_start_byte..first_span.start()])
                + (line_num_digits + "| ".len()),
        ));
        // Draw underlines between start()..end() and indent up to the the start of the next span.
        while let Some(span) = spans.next() {
            out.push_str(
                &underline_c
                    .to_string()
                    .repeat(UnicodeWidthStr::width(&self.src[span.start()..span.end()]).max(1)),
            );
            if let Some(next_span) = spans.peek() {
                out.push_str(&" ".repeat(UnicodeWidthStr::width(
                    &self.src[span.end()..next_span.start()],
                )));
            }
        }
        // With all the underlines drawn append the message.
        out.push_str(&format!(" {msg}"));
        out
    }

    pub fn format_conflicts<LexerTypesT>(
        &self,
        grm: &YaccGrammar<LexerTypesT::StorageT>,
        ast: &GrammarAST,
        c: &Conflicts<LexerTypesT::StorageT>,
        _sgraph: &lrtable::StateGraph<LexerTypesT::StorageT>,
        _stable: &lrtable::StateTable<LexerTypesT::StorageT>,
    ) -> String
    where
        LexerTypesT: LexerTypes,
        usize: num_traits::AsPrimitive<LexerTypesT::StorageT>,
    {
        let mut out = String::new();
        for (t_idx, r1_prod_idx, r2_prod_idx, _st_idx) in c.rr_conflicts() {
            let (_r1_prod_names, _r1_prod_spans) = pidx_prods_data(ast, *r1_prod_idx);
            let (_r2_prod_names, _r2_prod_spans) = pidx_prods_data(ast, *r2_prod_idx);

            let (t_name, t_span) = if let Some(name) = grm.token_name(*t_idx) {
                (name, grm.token_span(*t_idx))
            } else {
                (
                    "$",
                    grm.token_idx("$").and_then(|t_idx| grm.token_span(t_idx)),
                )
            };
            let r1_rule_idx = grm.prod_to_rule(*r1_prod_idx);
            let r2_rule_idx = grm.prod_to_rule(*r2_prod_idx);
            let r1_span = grm.rule_name_span(r1_rule_idx);
            let r2_span = grm.rule_name_span(r2_rule_idx);
            let r1_name = grm.rule_name_str(r1_rule_idx);
            let r2_name = grm.rule_name_str(r2_rule_idx);

            out.pushln(
                self.file_location_msg(
                    format!(
                        "Reduce/Reduce conflict, can reduce '{}' or '{}' with lookahead '{}'",
                        r1_name, r2_name, t_name,
                    )
                    .as_str(),
                    Some(r1_span),
                ),
            );
            out.pushln(self.underline_span_with_text(r1_span, "First reduce".to_string(), '^'));
            out.pushln(self.underline_span_with_text(r2_span, "Second reduce".to_string(), '^'));
            if let Some(t_span) = t_span {
                out.pushln(self.underline_span_with_text(t_span, "Lookahead".to_string(), '^'));
            }
            out.push('\n');
        }
        for (s_tok_idx, r_prod_idx, _st_idx) in c.sr_conflicts() {
            let r_rule_idx = grm.prod_to_rule(*r_prod_idx);
            let r_rule_span = grm.rule_name_span(r_rule_idx);
            let s_tok_span = grm.token_span(*s_tok_idx).unwrap();
            let shift_name = grm.token_name(*s_tok_idx).unwrap();
            let reduce_name = grm.rule_name_str(r_rule_idx);
            let (_r_prod_names, mut r_prod_spans) = pidx_prods_data(ast, *r_prod_idx);
            let fallback_span = ast.prods[usize::from(*r_prod_idx)].prod_span;
            out.pushln(
                self.file_location_msg(
                    format!(
                        "Shift/Reduce conflict, can shift '{}' or reduce '{}'",
                        shift_name, reduce_name
                    )
                    .as_str(),
                    Some(r_rule_span),
                ),
            );

            out.pushln(self.underline_span_with_text(s_tok_span, "Shift".to_string(), '^'));
            out.pushln(self.underline_span_with_text(r_rule_span, "Reduced rule".to_string(), '^'));

            if r_prod_spans.is_empty() {
                r_prod_spans.push(fallback_span);
            }

            let mut prod_lines = r_prod_spans
                .iter()
                .map(|span| self.nlc().span_line_bytes(*span))
                .collect::<Vec<_>>();
            prod_lines.sort();
            prod_lines.dedup();

            for lines in &prod_lines {
                let mut spans_on_line = Vec::new();
                for span in &r_prod_spans {
                    if lines == &self.nlc().span_line_bytes(*span) {
                        spans_on_line.push(*span)
                    }
                }

                let msg = if Some(lines) == prod_lines.last() {
                    "Reduced productions"
                } else {
                    ""
                };
                // We don't actually enforce left-to-right or non-overlapping,
                // It appears that the spans always have these properties.
                // but we lack an `Ord` impl to easily ensure it.
                //
                // We could convert to tuples, then back to spans or add the impl
                out.pushln(self.underline_spans_on_line_with_text(
                    spans_on_line.iter().copied(),
                    msg.to_string(),
                    '-',
                ));
            }
            out.push('\n');
        }
        out
    }
}

pub trait DiagnosticFormatter {
    fn format_error<E>(&self, e: E) -> Box<dyn Error>
    where
        E: Spanned + Error;
    fn format_warning<W>(&self, e: W) -> String
    where
        W: Spanned + Display;
}

impl DiagnosticFormatter for SpannedDiagnosticFormatter<'_> {
    fn format_error<E>(&self, e: E) -> Box<dyn Error>
    where
        E: Spanned + Error,
    {
        self.format_spanned(&e).into()
    }

    fn format_warning<W>(&self, w: W) -> String
    where
        W: Spanned + Display,
    {
        self.format_spanned(&w)
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use std::path::PathBuf;

    #[test]
    fn underline_multiline_span_test() {
        let s = "\naaaaaabbb\nbbb\nbbbb\n";
        let test_path = PathBuf::from("test");
        let formatter = SpannedDiagnosticFormatter::new(s, &test_path);

        let span = Span::new(7, 7 + 12);
        let out = format!(
            "\n{}",
            formatter.underline_span_with_text(span, "Test message".into(), '-')
        );
        assert_eq!(
            out,
            r"
2| aaaaaabbb
         ---
3| bbb
   ---
4| bbbb
   ---- Test message"
        );

        let out = format!(
            "\n{}",
            formatter.underline_span_with_text(span, "Test message".into(), '^')
        );
        assert_eq!(
            out,
            r"
2| aaaaaabbb
         ^^^
3| bbb
   ^^^
4| bbbb
   ^^^^ Test message"
        );
    }

    #[test]
    fn underline_single_line_span_test() {
        let s = "\naaaaaabbb bbb bbbb\n";
        let test_path = PathBuf::from("test");
        let formatter = SpannedDiagnosticFormatter::new(s, &test_path);

        let span = Span::new(7, 7 + 12);
        let out = format!(
            "\n{}",
            formatter.underline_span_with_text(span, "Test message".into(), '-')
        );
        assert_eq!(
            out,
            r"
2| aaaaaabbb bbb bbbb
         ------------ Test message"
        );
        let out = format!(
            "\n{}",
            formatter.underline_span_with_text(span, "Test message".into(), '^')
        );
        assert_eq!(
            out,
            r"
2| aaaaaabbb bbb bbbb
         ^^^^^^^^^^^^ Test message"
        );
    }

    #[test]
    fn span_prefix() {
        let s = "\naaaaaabbb\nbbb\nbbbb\n";
        let test_path = PathBuf::from("test");
        let formatter = SpannedDiagnosticFormatter::new(s, &test_path);
        // For raw string alignment.
        let mut out = String::from("\n");
        // On occasion we want dots to signal that the lines are not contiguous.
        out.push_str(&formatter.prefixed_underline_span_with_text(
            "...",
            Span::new(7, 10),
            "Test message".to_string(),
            '^',
        ));
        out.push('\n');
        // Skip over the middle set of b's.
        out.push_str(&formatter.underline_span_with_text(
            Span::new(15, 19),
            "Other message".to_string(),
            '-',
        ));
        assert_eq!(
            out,
            r"
2| aaaaaabbb
...      ^^^ Test message
4| bbbb
   ---- Other message"
        );
    }

    #[test]
    fn span_prefix_2() {
        let s = "\n\n\n\n\n\n\n\n\n\n\naaaaaabbb\nbbb\nbbbb\n";
        let test_path = PathBuf::from("test");
        let formatter = SpannedDiagnosticFormatter::new(s, &test_path);
        let mut out = String::from("\n");
        // On occasion we want dots to signal that the lines are not contiguous.
        out.push_str(&formatter.prefixed_underline_span_with_text(
            "...",
            Span::new(17, 20),
            "Test message".to_string(),
            '^',
        ));
        out.push('\n');
        // Skip over the middle set of b's.
        out.push_str(&formatter.underline_span_with_text(
            Span::new(25, 29),
            "Other message".to_string(),
            '-',
        ));
        assert_eq!(
            out,
            r"
12| aaaaaabbb
...       ^^^ Test message
14| bbbb
    ---- Other message"
        );
    }

    #[test]
    fn span_multiline_unicode() {
        let crabs = " 🦀🦀🦀 ";
        let crustaceans = format!("\"{crabs}\n{crabs}\"");
        let test_path = PathBuf::from("test");
        let formatter = SpannedDiagnosticFormatter::new(&crustaceans, &test_path);
        // For raw string alignment.
        let mut out = String::from("\n");
        out.push_str(&formatter.underline_span_with_text(
            Span::new(0, crabs.len() * 2 + "\n\"\"".len()),
            "Test".to_string(),
            '^',
        ));
        assert_eq!(
            out,
            r#"
1| " 🦀🦀🦀 
   ^^^^^^^^^
2|  🦀🦀🦀 "
   ^^^^^^^^^ Test"#
        );
    }

    #[test]
    fn span_unicode() {
        let crab = "\n🦀";
        let lobster = "🦞";
        let crustaceans = format!("{crab}{lobster}{crab}{crab}{lobster}");
        let test_path = PathBuf::from("test");
        let formatter = SpannedDiagnosticFormatter::new(&crustaceans, &test_path);
        // For raw string alignment.
        let mut out = String::from("\n");
        out.push_str(&formatter.prefixed_underline_span_with_text(
            "...",
            Span::new(crab.len(), crab.len() + lobster.len()),
            "Not a crab".to_string(),
            '^',
        ));
        out.push('\n');
        out.push_str(&formatter.underline_span_with_text(
            Span::new(
                crab.len() * 3 + lobster.len(),
                crab.len() * 3 + lobster.len() * 2,
            ),
            "Not a crab either".to_string(),
            '-',
        ));
        assert_eq!(
            out,
            r"
2| 🦀🦞
...  ^^ Not a crab
4| 🦀🦞
     -- Not a crab either"
        );
    }

    #[test]
    fn underline_single_line_spans_test() {
        let s = "\naaaaaabbb bbb bbbb\n";
        let test_path = PathBuf::from("test");
        let formatter = SpannedDiagnosticFormatter::new(s, &test_path);
        let spans = [(7, 10), (11, 14), (15, 19)]
            .iter()
            .map(|(i, j): &(usize, usize)| Span::new(*i, *j));
        let out = format!(
            "\n{}",
            formatter.underline_spans_on_line_with_text(
                spans.clone(),
                "Multiple spans on one line.".into(),
                '-'
            )
        );
        assert_eq!(
            out,
            r"
2| aaaaaabbb bbb bbbb
         --- --- ---- Multiple spans on one line."
        );
        let out = format!(
            "\n{}",
            formatter.underline_spans_on_line_with_text(
                spans,
                "Multiple spans on one line 2.".into(),
                '^'
            )
        );
        assert_eq!(
            out,
            r"
2| aaaaaabbb bbb bbbb
         ^^^ ^^^ ^^^^ Multiple spans on one line 2."
        );
        let spans = [(7usize, 10usize), (10, 14), (14, 19)]
            .iter()
            .map(|(i, j): &(usize, usize)| Span::new(*i, *j));
        let out = format!(
            "\n{}",
            formatter.underline_spans_on_line_with_text(
                spans,
                "Contiguous but non-overlapping".into(),
                '+'
            )
        );
        assert_eq!(
            out,
            r"
2| aaaaaabbb bbb bbbb
         ++++++++++++ Contiguous but non-overlapping"
        );
    }

    #[test]
    fn underline_single_line_spans_unicode() {
        let crab = "🦀";
        let lobster = "🦞";
        let crustaceans = format!("{crab}{lobster}{crab}{lobster}");
        let test_path = PathBuf::from("test");
        let formatter = SpannedDiagnosticFormatter::new(&crustaceans, &test_path);
        // For raw string alignment.
        let mut out = String::from("\n");
        let spans = [
            (crab.len(), crab.len() + lobster.len()),
            (
                crab.len() * 2 + lobster.len(),
                crab.len() * 2 + lobster.len() * 2,
            ),
        ];
        let spans = spans
            .iter()
            .map(|(start, end): &(usize, usize)| Span::new(*start, *end));
        out.push_str(&formatter.underline_spans_on_line_with_text(
            spans.clone(),
            "Not crabs".to_string(),
            '^',
        ));
        assert_eq!(
            out,
            r"
1| 🦀🦞🦀🦞
     ^^  ^^ Not crabs"
        );
    }

    #[test]
    fn underline_zero_length() {
        let s = r#"Error is between the quotes "" there"#;
        let test_path = PathBuf::from("test");
        let formatter = SpannedDiagnosticFormatter::new(&s, &test_path);
        let mut out = String::from("\n");
        let pos = s.find("\"").unwrap() + 1;
        out.push_str(&formatter.prefixed_underline_span_with_text(
            "",
            Span::new(pos, pos),
            "Here".to_string(),
            '^',
        ));
        assert_eq!(
            out,
            r#"
1| Error is between the quotes "" there
                                ^ Here"#
        );
    }
}
