#[cfg(wasm32_unknown)]
use wasm_bindgen::prelude::*;

use lrlex::lrlex_mod;
use lrpar::lrpar_mod;

// Using `lrlex_mod!` brings the lexer for `calc.l` into scope. By default the module name will be
// `calc_l` (i.e. the file name, minus any extensions, with a suffix of `_l`).
lrlex_mod!("calc_wasm.l");
// Using `lrpar_mod!` brings the parser for `calc.y` into scope. By default the module name will be
// `calc_y` (i.e. the file name, minus any extensions, with a suffix of `_y`).
lrpar_mod!("calc_wasm.y");

#[cfg_attr(wasm32_unknown, wasm_bindgen)]
#[allow(unused)]
pub fn calculate(l: &str) -> Result<u64, String> {
    // Get the `LexerDef` for the `calc` language.
    let lexerdef = calc_wasm_l::lexerdef();
    if l.trim().is_empty() {
        return Err("input is empty".to_string());
    }
    // Now we create a lexer with the `lexer` method with which we can lex an input.
    let lexer = lexerdef.lexer(l);
    // Pass the lexer to the parser and lex and parse the input.
    let (res, errs) = calc_wasm_y::parse(&lexer);
    if !errs.is_empty() {
        let mut ret = String::new();
        for e in errs {
            use lrpar::LexParseError;
            match e {
                LexParseError::ParseError(e) => {
                    let repairs_flag = !e.repairs().is_empty();
                    ret.push_str(&format!("Error: {}\n Repairs: {}", e, repairs_flag));
                }
                e => ret.push_str(&format!("{}\n", e)),
            };
        }
        if let Some(Err(e)) = res {
            ret.push_str(&format!("{}\n", e));
        }
        return Err(ret);
    }
    match res {
        Some(Ok(r)) => Ok(r),
        Some(Err(e)) => Err(e.to_string()),
        None => Err("Unable to parse".to_string()),
    }
}

#[cfg(test)]
mod test {
    use super::calculate;
    #[cfg(wasm32_unknown)]
    use wasm_bindgen_test::*;

    #[cfg_attr(wasm32_unknown, wasm_bindgen_test)]
    #[test]
    fn test_calc_14() {
        assert_eq!(calculate("2 + 3 * 4").unwrap(), 14);
    }

    #[cfg_attr(wasm32_unknown, wasm_bindgen_test)]
    #[test]
    fn test_lex_error() {
        assert!(calculate("#1 + #2").is_err());
    }

    #[cfg_attr(wasm32_unknown, wasm_bindgen_test)]
    #[test]
    fn test_recovery() {
        // We really want to test this recovery path, since it contains
        // calls to `Instant::now()` which panics on `std`
        // Thus we need to check that the `web_time` crate is working.
        let x = calculate("1+");
        match x {
            Err(e) => assert!(e.contains("Repairs: true")),
            Ok(e) => panic!("unexpectedly parsed {}", e),
        }
    }
}
