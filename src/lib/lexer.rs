use ast::LexAST;

#[derive(Debug)]
pub struct Lexeme {
    pub rule_idx: usize,
    /// Byte offset of the start of the lexeme
    pub start: usize,
    /// Length in bytes of the lexeme
    pub len: usize
}

#[derive(Debug)]
pub struct LexError {
    idx: usize
}

pub fn lex(ast: &LexAST, s: &str) -> Result<Vec<Lexeme>, LexError> {
    let mut i = 0; // byte index into s
    let mut lxs = Vec::new(); // lexemes
    'n: while i < s.len() {
        for (r_idx, r) in ast.rules.iter().enumerate() {
            match r.re.find(&s[i..]) {
                None => continue,
                Some(m) => {
                    if r.name.is_some() {
                        lxs.push(Lexeme{rule_idx: r_idx, start: i, len: m.end()});
                    }
                    i += m.end();
                    continue 'n;
                }
            }
        }
        return Err(LexError{idx: i});
    }
    Ok(lxs)
}

#[cfg(test)]
mod test {
    use std::collections::HashMap;
    use super::*;
    use parser::parse_lex;

    #[test]
    fn test_basic() {
        let src = r"
%%
[0-9]+ int
[a-zA-Z]+ id
[ \t] ;
        ".to_string();
        let mut ast = parse_lex(&src).unwrap();
        let mut map = HashMap::new();
        map.insert("int", 0);
        map.insert("id", 1);
        ast.set_rule_ids(&map);

        let lexemes = lex(&ast, "abc 123").unwrap();
        assert_eq!(lexemes.len(), 2);
        let lex1 = lexemes.get(0).unwrap();
        assert_eq!(lex1.rule_idx, 1);
        assert_eq!(lex1.start, 0);
        assert_eq!(lex1.len, 3);
        let lex2 = lexemes.get(1).unwrap();
        assert_eq!(lex2.rule_idx, 0);
        assert_eq!(lex2.start, 4);
        assert_eq!(lex2.len, 3);
    }


    #[test]
    fn test_basic_error() {
        let src = "
%%
[0-9]+ int
        ".to_string();
        let ast = parse_lex(&src).unwrap();
        match lex(&ast, "abc") {
            Ok(_)  => panic!("Invalid input lexed"),
            Err(LexError{idx: 0}) => (),
            Err(e) => panic!("Incorrect error returned {:?}", e)
        };
    }
}
