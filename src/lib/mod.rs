pub mod grammar;
mod yacc;

use grammar::Grammar;

pub fn parse_yacc<'a>(s:&'a String) -> Grammar {
    yacc::parse(s.to_string())
}

