use std::{error::Error, fmt::Display, path::Path, str::FromStr};

use cfgrammar::{newlinecache::NewlineCache, yacc::parser::SpansKind, Span, Spanned};
use unicode_width::UnicodeWidthStr;

pub struct SpannedDiagnosticFormatter<'a> {
    src: &'a str,
    path: &'a Path,
    nlc: NewlineCache,
}

impl<'a> SpannedDiagnosticFormatter<'a> {
    #[allow(clippy::result_unit_err)]
    pub fn new(src: &'a str, path: &'a Path) -> Result<Self, ()> {
        Ok(Self {
            src,
            path,
            nlc: NewlineCache::from_str(src)?,
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
                .nlc
                .byte_to_line_num_and_col_num(self.src, span.start())
                .unwrap_or((0, 0));
            format!("{} at {}:{line}:{col}", msg, self.path.display())
        } else {
            format!("{} in {}", msg, self.path.display())
        }
    }

    /// Print the line/column information and source text for all lines intersecting the span.
    /// Underline the portion covered by the span with the `underline_c` character.
    #[allow(unused)]
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
        let (start_byte, end_byte) = self.nlc.span_line_bytes(span);
        // Produce an underline underneath a span which may cover multiple lines, and a message on the last line.
        let mut source_lines = self.src[start_byte..end_byte].lines().peekable();
        while let Some(source_line) = source_lines.next() {
            let (line_start_byte, _) = self.nlc.span_line_bytes(span);
            let span_offset_from_start = span.start() - line_start_byte;

            // An underline bounded by the current line.
            let underline_span = Span::new(
                span.start(),
                span.end()
                    .min(span.start() + (source_line.len() - span_offset_from_start)),
            );
            let (line_num, _) = self
                .nlc
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
            out.push_str(&(underline_c.to_string()).repeat(UnicodeWidthStr::width(
                &self.src[underline_span.start()..underline_span.end()],
            )));

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
                .nlc
                .byte_to_line_num_and_col_num(self.src, span.start())
                .unwrap_or((0, 0));
            let next_line = spans
                .peek()
                .map(|(_, span)| span)
                .map(|s| self.nlc.byte_to_line_num(s.start()).unwrap_or(line))
                .unwrap_or(line);
            // Is this line contiguous with the next, if not prefix it with dots.
            let dots = if next_line - line > 1 { "..." } else { "" };
            if span_num == 0 {
                let s = e.to_string();
                out.push_str(&self.prefixed_underline_span_with_text(dots, *span, s, '^'));
            } else {
                let s = match e.spanskind() {
                    SpansKind::DuplicationError => {
                        format!("{} occurrence", Self::ordinal(span_num + 1))
                    }
                    SpansKind::Error => {
                        unreachable!("Should contain a single span at the site of the error")
                    }
                };
                out.push_str(&self.prefixed_underline_span_with_text(dots, *span, s, '-'));
            }
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
        let formatter = SpannedDiagnosticFormatter::new(s, &test_path).unwrap();

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
        let formatter = SpannedDiagnosticFormatter::new(s, &test_path).unwrap();

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
        let formatter = SpannedDiagnosticFormatter::new(s, &test_path).unwrap();
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
        let formatter = SpannedDiagnosticFormatter::new(s, &test_path).unwrap();
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
        let formatter = SpannedDiagnosticFormatter::new(&crustaceans, &test_path).unwrap();
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
        let formatter = SpannedDiagnosticFormatter::new(&crustaceans, &test_path).unwrap();
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
}
