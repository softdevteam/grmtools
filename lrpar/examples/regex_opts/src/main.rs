use std::io::{self, Read};

use lrlex::lrlex_mod;
use lrpar::lrpar_mod;

lrlex_mod!("any.l");
lrpar_mod!("any.y");

fn main() -> Result<(), std::io::Error> {
    // Get the `LexerDef` for the `calc` language.
    let lexerdef = any_l::lexerdef();
    let stdin = io::stdin();
    let mut s = String::new();
    stdin.lock().read_to_string(&mut s)?;
    let lexer = lexerdef.lexer(&s);
    let (res, errs) = any_y::parse(&lexer);
    for e in errs {
        println!("{}", e.pp(&lexer, &any_y::token_epp));
    }
    Ok(println!("{:?}", res))
}
