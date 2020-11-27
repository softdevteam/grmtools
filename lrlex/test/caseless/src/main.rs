//use lrlex::{LexerBuilder, LexerKind};
use lrlex::{
    lrlex_mod,
    LexerDef
};
use lrpar::lex::Lexer;
use std::{
    fs::File,
    process,
    io::{
        Read,
        Write,
        stderr
    }
};

lrlex_mod!("java.l");

fn main() {

    let lexerdef = java_l::lexerdef();
    let mut f = match File::open("C.java") {
        Ok(r) => r,
        Err(e) => {
            writeln!(&mut stderr(), "Can't open file C.java: {}", e).ok();
            process::exit(1);
        }
    };
    let mut s = String::new();
    f.read_to_string(&mut s).unwrap();
    let input = s;

    for r in lexerdef.lexer(&input).iter() {
        match r {
            Ok(l) => println!(
                "{} {}",
                lexerdef.get_rule_by_id(l.tok_id()).name.as_ref().unwrap(),
                &input[l.span().start()..l.span().end()]
            ),
            Err(e) => {
                println!("{:?}", e);
                process::exit(1);
            }
        }
    }



    // let java_l = match LexerBuilder::<u32>::new()
    //     .lexerkind(LexerKind::Flex)
    //     .process_file_in_src("java.l") {
    //     Ok(r) => r,
    //     Err(_) => panic!("Oops")
    // };

}
