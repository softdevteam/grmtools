#[cfg(test)]
use cfgrammar::Span;

mod cgen_helper;
#[allow(unused)]
use cgen_helper::run_test_path;

mod calc_wasm;

#[cfg(test)]
use cttests_macro::generate_codegen_fail_tests;
use lrlex::lrlex_mod;
use lrpar::lrpar_mod;
#[cfg(test)]
use lrpar::{Lexeme, Lexer, NonStreamingLexer};

lrlex_mod!("calc_multitypes.l");
lrpar_mod!("calc_multitypes.y");

lrlex_mod!("calc_actiontype.l");
lrpar_mod!("calc_actiontype.y");

lrlex_mod!("calc_noactions.l");
lrpar_mod!("calc_noactions.y");

lrlex_mod!("calc_nodefault_yacckind.l");
lrpar_mod!("calc_nodefault_yacckind.y");

lrlex_mod!("calc_unsafeaction.l");
lrpar_mod!("calc_unsafeaction.y");

lrlex_mod!("expect.l");
lrpar_mod!("expect.y");

lrlex_mod!("lexer_lifetime.l");
lrpar_mod!("lexer_lifetime.y");

lrlex_mod!("lex_flags.l");
lrpar_mod!("lex_flags.y");

lrlex_mod!("multitypes.l");
lrpar_mod!("multitypes.y");

lrlex_mod!("parseparam.l");
lrpar_mod!("parseparam.y");

lrlex_mod!("parseparam_copy.l");
lrpar_mod!("parseparam_copy.y");

lrlex_mod!("passthrough.l");
lrpar_mod!("passthrough.y");

lrlex_mod!("regex_opt.l");
lrlex_mod!("regex_opt.y");

lrlex_mod!("span.l");
lrpar_mod!("span.y");

lrlex_mod!("storaget.l");
lrpar_mod!("storaget.y");

lrlex_mod!("grmtools_section.l");
lrpar_mod!("grmtools_section.y");

#[test]
fn multitypes() {
    let lexerdef = multitypes_l::lexerdef();
    let lexer = lexerdef.lexer("aa");
    let (r, errs) = multitypes_y::parse(&lexer);
    assert_eq!(r.unwrap().len(), 2);
    assert_eq!(errs.len(), 0);
}

#[test]
fn test_no_actions() {
    let lexerdef = calc_noactions_l::lexerdef();
    let lexer = lexerdef.lexer("2+3");
    if !calc_noactions_y::parse(&lexer).is_empty() {
        panic!();
    }
    let lexer = lexerdef.lexer("2++3");
    if calc_noactions_y::parse(&lexer).len() != 1 {
        panic!();
    }
}

#[test]
fn test_basic_actions() {
    let lexerdef = calc_actiontype_l::lexerdef();
    let lexer = lexerdef.lexer("2+3");
    match calc_actiontype_y::parse(&lexer) {
        (Some(Ok(5)), ref errs) if errs.is_empty() => (),
        _ => unreachable!(),
    }
}

#[test]
fn test_nodefault_yacckind() {
    let lexerdef = calc_nodefault_yacckind_l::lexerdef();
    let lexer = lexerdef.lexer("2+3");
    match calc_nodefault_yacckind_y::parse(&lexer) {
        (Some(Ok(5)), ref errs) if errs.is_empty() => (),
        _ => unreachable!(),
    }
}
#[test]
fn test_unsafe_actions() {
    let lexerdef = calc_unsafeaction_l::lexerdef();
    let lexer = lexerdef.lexer("2+3");
    match calc_unsafeaction_y::parse(&lexer) {
        (Some(Ok(5)), ref errs) if errs.is_empty() => (),
        _ => unreachable!(),
    }
}

#[test]
fn test_error_recovery_and_actions() {
    use lrpar::LexParseError;

    let lexerdef = calc_actiontype_l::lexerdef();

    let lexer = lexerdef.lexer("2++3");
    let (r, errs) = calc_actiontype_y::parse(&lexer);
    match r {
        Some(Ok(5)) => (),
        _ => unreachable!(),
    }
    match errs[0] {
        LexParseError::ParseError(..) => (),
        _ => unreachable!(),
    }

    let lexer = lexerdef.lexer("2+3)");
    let (r, errs) = calc_actiontype_y::parse(&lexer);
    assert_eq!(r, Some(Ok(5)));
    assert_eq!(errs.len(), 1);
    match errs[0] {
        LexParseError::ParseError(..) => (),
        _ => unreachable!(),
    }

    let lexer = lexerdef.lexer("2+3+18446744073709551616");
    let (r, errs) = calc_actiontype_y::parse(&lexer);
    assert_eq!(r, Some(Err(())));
    assert!(errs.is_empty());
}

#[test]
fn test_calc_multitypes() {
    let lexerdef = calc_multitypes_l::lexerdef();
    let lexer = lexerdef.lexer("1+2*3");
    let (res, _errs) = calc_multitypes_y::parse(&lexer);
    assert_eq!(res, Some(Ok(7)));

    let lexer = lexerdef.lexer("1++2");
    let (res, _errs) = calc_multitypes_y::parse(&lexer);
    assert_eq!(res, Some(Ok(3)));
}

#[test]
fn test_input_lifetime() {
    // This test only exists to make sure that this code compiles: there's no need for us to
    // actually run anything.
    let lexerdef = lexer_lifetime_l::lexerdef();
    let input = "a";
    let _ = {
        let lexer = lexerdef.lexer(input);
        let lx = lexer.iter().next().unwrap().unwrap();
        lexer.span_str(lx.span())
    };
}

#[test]
fn test_lexer_lifetime() {
    // This test only exists to make sure that this code compiles: there's no need for us to
    // actually run anything.

    #[allow(clippy::needless_lifetimes)]
    pub(crate) fn parse_data<'a>(input: &'a str) -> Option<&'a str> {
        let lexer_def = crate::lexer_lifetime_l::lexerdef();
        let l = lexer_def.lexer(input);
        match crate::lexer_lifetime_y::parse(&l) {
            (Option::Some(x), _) => Some(x),
            _ => None,
        }
    }
    parse_data("abc");
}

#[test]
fn test_span() {
    let lexerdef = span_l::lexerdef();
    let lexer = lexerdef.lexer("2+3");
    match span_y::parse(&lexer) {
        (Some(ref spans), _)
            if spans
                == &vec![
                    Span::new(0, 1),
                    Span::new(0, 1),
                    Span::new(0, 1),
                    Span::new(2, 3),
                    Span::new(2, 3),
                    Span::new(0, 3),
                ] => {}
        _ => unreachable!(),
    }

    let lexer = lexerdef.lexer("2 + 3");
    match span_y::parse(&lexer) {
        (Some(ref spans), _)
            if spans
                == &vec![
                    Span::new(0, 1),
                    Span::new(0, 1),
                    Span::new(0, 1),
                    Span::new(4, 5),
                    Span::new(4, 5),
                    Span::new(0, 5),
                ] => {}
        _ => unreachable!(),
    }

    let lexer = lexerdef.lexer("2+3*4");
    match span_y::parse(&lexer) {
        (Some(ref spans), _)
            if spans
                == &vec![
                    Span::new(0, 1),
                    Span::new(0, 1),
                    Span::new(0, 1),
                    Span::new(2, 3),
                    Span::new(2, 3),
                    Span::new(4, 5),
                    Span::new(2, 5),
                    Span::new(0, 5),
                ] => {}
        _ => unreachable!(),
    }

    let lexer = lexerdef.lexer("2++3");
    match span_y::parse(&lexer) {
        (Some(ref spans), _)
            if spans
                == &vec![
                    Span::new(0, 1),
                    Span::new(0, 1),
                    Span::new(0, 1),
                    Span::new(3, 4),
                    Span::new(3, 4),
                    Span::new(0, 4),
                ] => {}
        _ => unreachable!(),
    }

    let lexer = lexerdef.lexer("(2)))");
    match dbg!(span_y::parse(&lexer)) {
        (Some(ref spans), _)
            if spans
                == &vec![
                    Span::new(1, 2),
                    Span::new(1, 2),
                    Span::new(1, 2),
                    Span::new(0, 3),
                    Span::new(0, 3),
                    Span::new(0, 3),
                ] => {}
        _ => unreachable!(),
    }
}

#[test]
fn test_parseparam() {
    let lexerdef = parseparam_l::lexerdef();
    let lexer = lexerdef.lexer("101");
    match parseparam_y::parse(&lexer, &3) {
        (Some(104), _) => (),
        _ => unreachable!(),
    }
}

#[test]
fn test_parseparam_copy() {
    let lexerdef = parseparam_copy_l::lexerdef();
    let lexer = lexerdef.lexer("101");
    match parseparam_copy_y::parse(&lexer, 3) {
        (Some(104), _) => (),
        _ => unreachable!(),
    }
}

#[test]
fn test_passthrough() {
    let lexerdef = passthrough_l::lexerdef();
    let lexer = lexerdef.lexer("101");
    match passthrough_y::parse(&lexer) {
        (Some(Ok(ref s)), _) if s == "$101" => (),
        _ => unreachable!(),
    }
}

#[test]
fn test_storaget() {
    let lexerdef = storaget_l::lexerdef();
    let lexer = lexerdef.lexer("glasses, keys, umbrella");
    let expect = ["glasses", "keys", "umbrella"]
        .iter()
        .map(|x| x.to_string())
        .collect::<Vec<_>>();
    let (val, e) = storaget_y::parse(&lexer);
    assert_eq!(val, Some(expect));
    assert!(e.is_empty());
}

#[test]
fn test_expect() {
    // This test merely needs to compile in order to be successful.
}

// This test isn't run on wasm32-wasi because it accesses
// various files from across the project workspace.
//
// Wasi's filesystem access is sandboxed by default.
#[test]
fn test_grmtools_section_files() {
    use glob::glob;
    use std::env;
    use std::fs::File;
    use std::io::BufReader;
    use std::io::{BufRead as _, Read as _};

    let manifest_dir = env::var("CARGO_MANIFEST_DIR").unwrap();
    let examples_glob = format!("{manifest_dir}/../examples/**");
    let examples_l_glob = format!("{examples_glob}/*.l");
    let examples_y_glob = format!("{examples_glob}/*.y");
    let out_dir = env::var("OUT_DIR").unwrap();
    let cttests_l_glob = format!("{out_dir}/*.l");
    let cttests_y_glob = format!("{out_dir}/*.y");
    let files = glob(&examples_l_glob)
        .unwrap()
        .chain(glob(&examples_y_glob).unwrap())
        .chain(glob(&cttests_l_glob).unwrap())
        .chain(glob(&cttests_y_glob).unwrap())
        .collect::<Vec<_>>();
    assert!(!files.is_empty());
    for file_path in files {
        let file_path = file_path.unwrap();
        let mut s = String::new();
        let mut f = File::open(&file_path).unwrap();
        let _ = f.read_to_string(&mut s).unwrap();
        if s.starts_with("%grmtools") {
            let mut buf = Vec::new();
            let mut reader = BufReader::new(s.as_bytes());
            let _ = reader.read_until(b'}', &mut buf);
            let lexerdef = grmtools_section_l::lexerdef();
            let s = String::from_utf8(buf).unwrap();
            let l = lexerdef.lexer(&s);
            let (val, errs) = grmtools_section_y::parse(&l);
            if !errs.is_empty() {
                let mut s = "Errors:\n".to_string();
                for e in errs {
                    s.push_str(&format!("\t{}\n", e));
                }
                panic!("{}", s);
            } else {
                eprintln!("%grmtools {:?} {:?}", file_path.file_name(), val);
            }
        }
    }
}

#[test]
fn test_grmtools_section() {
    let srcs = [
        "%grmtools{}",
        "%grmtools{x}",
        "%grmtools{x,}",
        "%grmtools{!x}",
        "%grmtools{!x,}",
        "%grmtools{x: y}",
        "%grmtools{x: y,}",
        "%grmtools{x, y}",
        "%grmtools{x, y,}",
        "%grmtools{x, !y}",
        "%grmtools{x, !y,}",
        "%grmtools{x: y(z)}",
        "%grmtools{x: y(z),}",
        "%grmtools{a, x: y(z),}",
        "%grmtools{a, x: y(z)}",
        "%grmtools{a, !b, x: y(z), e: f}",
        "%grmtools{a, !b, x: y(z), e: f,}",
    ];

    let lexerdef = grmtools_section_l::lexerdef();
    for src in srcs {
        let l = lexerdef.lexer(src);
        let (val, errs) = grmtools_section_y::parse(&l);
        if !errs.is_empty() {
            let mut s = "Errors:\n".to_string();
            for e in errs {
                s.push_str(&format!("\t{}\n", e));
            }
            panic!("{}", s);
        }
        println!("{:?}", val);
    }
}

// regex options set through the builder methods.
#[test]
fn test_regex_opt() {
    let lexerdef = regex_opt_l::lexerdef();
    let lexer = lexerdef.lexer("a");
    match regex_opt_y::parse(&lexer) {
        ref errs if errs.is_empty() => (),
        e => panic!("{:?}", e),
    }
}

// Lex flags set through the grmtools section.
#[test]
fn test_lex_flags() {
    let lexerdef = lex_flags_l::lexerdef();
    let lexer = lexerdef.lexer("a");
    match lex_flags_y::parse(&lexer) {
        ref errs if errs.is_empty() => (),
        e => panic!("{:?}", e),
    }
}

// Codegen failure tests
#[cfg(test)]
generate_codegen_fail_tests!("src/ctfails/*.test");
