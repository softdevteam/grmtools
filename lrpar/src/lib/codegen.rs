#![deny(unfulfilled_lint_expectations)]
#![expect(dead_code)]

use std::{error::Error, fmt, path::Path};

use cfgrammar::{
    Location, Span,
    header::{GrmtoolsSectionParser, Header},
};

use crate::{
    ctbuilder::ERROR,
    diagnostics::{DiagnosticFormatter, SpannedDiagnosticFormatter},
};

pub(crate) struct ParserSrcEnv<'a> {
    src: &'a str,
    // We store the path here so we can generate a module name from it if needed.
    // But should never use it for filesystem interaction within this module.
    path: &'a Path,
    diagnostics: SpannedDiagnosticFormatter<'a>,
    header: Header<Location>,
}

pub(crate) struct ParserCodegenArgs {}

pub(crate) struct ParserCodegen {}

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

    pub(crate) fn code_generator(
        &mut self,
        _args: ParserCodegenArgs,
    ) -> Result<ParserCodegen, Box<dyn Error>> {
        self.merge_headers()?;
        Ok(ParserCodegen {})
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
