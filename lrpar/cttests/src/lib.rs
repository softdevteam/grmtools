use lrlex::lrlex_mod;
use lrpar::lrpar_mod;
#[cfg(test)]
use lrpar::Span;
#[cfg(test)]
use lrpar::{Lexeme, Lexer, NonStreamingLexer};

lrlex_mod!("calc_multitypes.l");
lrpar_mod!("calc_multitypes.y");

lrlex_mod!("calc_actiontype.l");
lrpar_mod!("calc_actiontype.y");

lrlex_mod!("calc_noactions.l");
lrpar_mod!("calc_noactions.y");

lrlex_mod!("expect.l");
lrpar_mod!("expect.y");

lrlex_mod!("lexer_lifetime.l");
lrpar_mod!("lexer_lifetime.y");

lrlex_mod!("multitypes.l");
lrpar_mod!("multitypes.y");

lrlex_mod!("parseparam.l");
lrpar_mod!("parseparam.y");

lrlex_mod!("passthrough.l");
lrpar_mod!("passthrough.y");

lrlex_mod!("span.l");
lrpar_mod!("span.y");

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

    pub(crate) fn parse_data(input: &'_ str) -> Option<&'_ str> {
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
        (Some(i), _) if i == 104 => (),
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
fn test_expect() {
    // This test merely needs to compile in order to be successful.
}
