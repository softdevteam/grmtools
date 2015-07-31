pub mod grammar;
mod yacc;

use grammar::Grammar;
use yacc::YaccParser;

pub fn parse_yacc<'a>(s:&'a String) -> Grammar {
    let mut yp = YaccParser::new(s.to_string());
    yp.parse();
    yp.grammar
}

