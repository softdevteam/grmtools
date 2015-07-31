pub mod grammar;
use grammar::{Grammar, Symbol, SymbolType};

extern crate regex;
use regex::Regex;

pub fn parse_yacc<'a>(s:&'a String) -> Grammar {
    let mut yp = YaccParser::new(s.to_string());
    yp.parse();
    yp.grammar
}

struct YaccParser {
    src: String,
    pos: usize,
    grammar: Grammar
}

impl YaccParser {
    fn new(src: String) -> YaccParser {
        YaccParser {
            src: src,
            pos: 0,
            grammar: Grammar::new()
        }
    }

    fn remaining_src(&self) -> &str{
        &self.src[self.pos..self.src.len()]
    }

    fn parse(&mut self){
        self.parse_declarations();  // optional
        self.parse_rules();         // including %%
        self.parse_programs();      // optional
    }

    fn parse_declarations(&mut self) {
        self.parse_ws();
        loop {
            if self.lookahead_is("%%") {
                self.pos += 2;
                break;
            }
            match self.parse_declaration() {
                Ok(()) => (),
                Err(err) => panic!("{}", err)
            }
            self.parse_ws();
        }
    }

    fn parse_declaration(&mut self) -> Result<(), String>{
        if self.lookahead_is("%token") {
            self.pos += 6;
            loop {
                self.parse_ws();
                if self.lookahead_is("%"){
                    break;
                }
                let name = try!(self.parse_name());
                self.grammar.tokens.insert(name);
            }
            Ok(())
        }
        else if self.lookahead_is("%start") {
            self.pos += 6;
            self.parse_ws();
            let name = try!(self.parse_name());
            self.grammar.start = name;
            Ok(())
        }
        else {
            Err("Couldn't parse declaration!".to_string())
        }
    }

    fn parse_programs(&mut self) {
    }

    fn parse_ws(&mut self) {
        let re = Regex::new(r"^\s+").unwrap();
        let result = re.find(self.remaining_src());
        let (_, x2) = match result {
            Some(_) => result.unwrap(),
            None => return
        };
        self.pos += x2;
    }

    fn parse_name(&mut self) -> Result<String, String> {
        let re = Regex::new(r"^[a-zA-Z_][a-zA-Z0-9_]*").unwrap();
        let result = re.find(self.remaining_src());
        let (x1, x2) = match result {
            Some(_) => result.unwrap(),
            None => return Err("Couldn't parse name!".to_string())
        };

        let name = &self.src[self.pos+x1..self.pos+x2];
        self.pos += name.len();
        Ok(name.to_string())
    }

    fn parse_rules(&mut self) {
        self.parse_ws();
        loop {
            if self.pos >= self.src.len() {
                break;
            }
            if self.lookahead_is("%%") {
                self.pos += 2;
                break;
            }
            match self.parse_rule() {
                Ok(()) => (),
                Err(msg) => panic!("{}", msg)
            }
            self.parse_ws();
        }
    }

    fn parse_rule(&mut self) -> Result<(), String> {
        let name = try!(self.parse_name());
        self.parse_ws();
        try!(self.parse_string(":"));
        let mut empty = true;
        loop {
            self.parse_ws();
            if self.lookahead_is("|") {
                self.pos += 1;
                if empty {
                    self.grammar.add_rule(name.clone(),
                      vec!{Symbol{name: String::new(), typ: SymbolType::Epsilon}});
                }
                empty = true;
            }
            else if self.lookahead_is(";") {
                self.pos += 1;
                if empty {
                    self.grammar.add_rule(name.clone(), 
                      vec!{Symbol{name: String::new(), typ: SymbolType::Epsilon}});
                }
                break;
            }
            else {
                let symbols = try!(self.parse_symbols());
                self.grammar.add_rule(name.clone(), symbols);
                empty = false;
            }
        }
        Ok(())
    }

    fn parse_symbols(&mut self) -> Result<(Vec<Symbol>), String> {
        let mut v = Vec::new();
        loop {
            self.parse_ws();
            if self.lookahead_is(";") || self.lookahead_is("|") { // replace with lookahead
                break;
            }
            self.parse_ws();
            let symbol = try!(self.parse_symbol());
            v.push(symbol);
        }
        Ok(v)
    }

    fn parse_symbol(&mut self) -> Result<Symbol, String> {
        // try token
        let name;
        let typ;
        if self.lookahead_is("'") {
            try!(self.parse_string("'"));
            name = try!(self.parse_name());
            typ = SymbolType::Terminal;
            try!(self.parse_string("'"));
        }
        else if self.lookahead_is("\"") {
            try!(self.parse_string("\""));
            name = try!(self.parse_name());
            typ = SymbolType::Terminal;
            try!(self.parse_string("\""));
        }
        else {
            name = try!(self.parse_name());
            if self.grammar.has_token(&name) {
                typ = SymbolType::Terminal;
            }
            else {
                typ = SymbolType::Nonterminal;
            }
        }
        Ok(Symbol{name: name, typ: typ})
    }

    fn parse_string(&mut self, s: &str) -> Result<(), String> {
        let slice = &self.src[self.pos..self.pos + s.len()];
        if slice != s {
            return Err(format!("Failed parsing string '{}'", s));
        }
        self.pos += s.len();
        Ok(())
    }

    fn lookahead_is(&mut self, s: &str) -> bool {
        let slice = &self.src[self.pos..self.pos + s.len()];
        slice == s
    }
}
