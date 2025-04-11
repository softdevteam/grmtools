#![allow(clippy::unnecessary_wraps)]

use std::io::{self, Read};

use lrlex::lrlex_mod;
use lrpar::lrpar_mod;

lrlex_mod!("todo.l");
lrpar_mod!("todo.y");

// For the example within this bin see build.rs
fn main() {
    let lexerdef = todo_l::lexerdef();
    let mut input = String::new();
    let _ = io::stdin().read_to_string(&mut input).unwrap();
    let lexer = lexerdef.lexer(&input);
    let (node, errs) = todo_y::parse(&lexer);
    if let Some(node) = node {
        println!("{:?}", node);
    }
    for e in errs {
        eprintln!("Error: {}", e);
    }
}
