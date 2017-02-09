use ast::LexAST;

#[derive(Debug)]
pub struct Lexeme {
    pub tok_id: usize,
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

    while i < s.len() {
        let mut longest = 0; // Length of the longest match
        let mut longest_ridx = 0; // This is only valid iff longest != 0
        for (ridx, r) in ast.rules.iter().enumerate() {
            if let Some(m) = r.re.find(&s[i..]) {
                let len = m.end();
                // Note that by using ">", we implicitly prefer an earlier over a later rule, if
                // both match an input of the same length.
                if len > longest {
                    longest = len;
                    longest_ridx = ridx;
                }
            }
        }
        if longest > 0 {
            let r = ast.rules.get(longest_ridx).unwrap();
            if r.name.is_some() {
                lxs.push(Lexeme{tok_id: r.tok_id, start: i, len: longest});
            }
            i += longest;
        } else {
            return Err(LexError{idx: i});
        }
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
        assert_eq!(lex1.tok_id, 1);
        assert_eq!(lex1.start, 0);
        assert_eq!(lex1.len, 3);
        let lex2 = lexemes.get(1).unwrap();
        assert_eq!(lex2.tok_id, 0);
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

    #[test]
    fn test_longest_match() {
        let src = "%%
if IF
[a-z]+ ID
[ ] ;".to_string();
        let mut ast = parse_lex(&src).unwrap();
        let mut map = HashMap::new();
        map.insert("IF", 0);
        map.insert("ID", 1);
        ast.set_rule_ids(&map);

        let lexemes = lex(&ast, "iff if").unwrap();
        println!("{:?}", lexemes);
        assert_eq!(lexemes.len(), 2);
        let lex1 = lexemes.get(0).unwrap();
        assert_eq!(lex1.tok_id, 1);
        assert_eq!(lex1.start, 0);
        assert_eq!(lex1.len, 3);
        let lex2 = lexemes.get(1).unwrap();
        assert_eq!(lex2.tok_id, 0);
        assert_eq!(lex2.start, 4);
        assert_eq!(lex2.len, 2);
    }
}
