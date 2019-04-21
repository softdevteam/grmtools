use lrlex::lrlex_mod;
use lrpar::lrpar_mod;

lrlex_mod!(calc_multitypes_l);
lrpar_mod!(calc_multitypes_y);

lrlex_mod!(calc_actiontype_l);
lrpar_mod!(calc_actiontype_y);

lrlex_mod!(calc_noactions_l);
lrpar_mod!(calc_noactions_y);

lrlex_mod!(multitypes_l);
lrpar_mod!(multitypes_y);

lrlex_mod!(span_l);
lrpar_mod!(span_y);

#[test]
fn multitypes() {
    let lexerdef = multitypes_l::lexerdef();
    let mut lexer = lexerdef.lexer("aa");
    let (r, errs) = multitypes_y::parse(&mut lexer);
    assert_eq!(r.unwrap().len(), 2);
    assert_eq!(errs.len(), 0);
}

#[test]
fn test_no_actions() {
    let lexerdef = calc_noactions_l::lexerdef();
    let mut lexer = lexerdef.lexer("2+3");
    if !calc_noactions_y::parse(&mut lexer).is_empty() {
        panic!();
    }
    let mut lexer = lexerdef.lexer("2++3");
    if calc_noactions_y::parse(&mut lexer).len() != 1 {
        panic!();
    }
}

#[test]
fn test_basic_actions() {
    let lexerdef = calc_actiontype_l::lexerdef();
    let mut lexer = lexerdef.lexer("2+3");
    match calc_actiontype_y::parse(&mut lexer) {
        (Some(Ok(5)), ref errs) if errs.len() == 0 => (),
        _ => unreachable!()
    }
}

#[test]
fn test_error_recovery_and_actions() {
    use lrpar::LexParseError;

    let lexerdef = calc_actiontype_l::lexerdef();

    let mut lexer = lexerdef.lexer("2++3");
    let (r, errs) = calc_actiontype_y::parse(&mut lexer);
    match r {
        Some(Ok(5)) => (),
        _ => unreachable!()
    }
    match errs[0] {
        LexParseError::ParseError(..) => (),
        _ => unreachable!()
    }

    let mut lexer = lexerdef.lexer("2+3)");
    let (r, errs) = calc_actiontype_y::parse(&mut lexer);
    assert_eq!(r, Some(Ok(5)));
    assert_eq!(errs.len(), 1);
    match errs[0] {
        LexParseError::ParseError(..) => (),
        _ => unreachable!()
    }

    let mut lexer = lexerdef.lexer("2+3+18446744073709551616");
    let (r, errs) = calc_actiontype_y::parse(&mut lexer);
    assert_eq!(r, Some(Err(())));
    assert!(errs.is_empty());
}

#[test]
fn test_calc_multitypes() {
    let lexerdef = calc_multitypes_l::lexerdef();
    let mut lexer = lexerdef.lexer("1+2*3");
    let (res, _errs) = calc_multitypes_y::parse(&mut lexer);
    assert_eq!(res, Some(Ok(7)));

    lexer = lexerdef.lexer("1++2");
    let (res, _errs) = calc_multitypes_y::parse(&mut lexer);
    assert_eq!(res, Some(Ok(3)));
}

#[test]
fn test_span() {
    let lexerdef = span_l::lexerdef();
    let mut lexer = lexerdef.lexer("2+3");
    match span_y::parse(&mut lexer) {
        (Some(ref spans), _) if spans == &vec![(0, 1), (0, 1), (2, 3), (2, 3), (2, 3), (0, 3)] => {
            ()
        }
        _ => unreachable!()
    }

    let mut lexer = lexerdef.lexer("2+3*4");
    match span_y::parse(&mut lexer) {
        (Some(ref spans), _)
            if spans
                == &vec![
                    (0, 1),
                    (0, 1),
                    (2, 3),
                    (4, 5),
                    (4, 5),
                    (2, 5),
                    (2, 5),
                    (0, 5),
                ] =>
        {
            ()
        }
        _ => unreachable!()
    }

    let mut lexer = lexerdef.lexer("2++3");
    match span_y::parse(&mut lexer) {
        (Some(ref spans), _) if spans == &vec![(0, 1), (0, 1), (3, 4), (3, 4), (3, 4), (0, 4)] => {
            ()
        }
        _ => unreachable!()
    }

    let mut lexer = lexerdef.lexer("(2)))");
    match span_y::parse(&mut lexer) {
        (Some(ref spans), _) if spans == &vec![(1, 2), (1, 2), (1, 2), (0, 3), (0, 3), (0, 3)] => {
            ()
        }
        _ => unreachable!()
    }
}
