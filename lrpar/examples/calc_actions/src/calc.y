%start Expr
%avoid_insert "INT"
%%
Expr -> Result<u64, ()>:
      Term '+' Expr { Ok($1? + $3?) }
    | Term { $1 }
    ;

Term -> Result<u64, ()>:
      Factor '*' Term { Ok($1? * $3?) }
    | Factor { $1 }
    ;

Factor -> Result<u64, ()>:
      '(' Expr ')' { $2 }
    | 'INT'
      {
          let v = $1.map_err(|_| ())?;
          parse_int($lexer.lexeme_str(&v))
      }
    ;
%%
// Any functions here are in scope for all the grammar actions above.

fn parse_int(s: &str) -> Result<u64, ()> {
    match s.parse::<u64>() {
        Ok(val) => Ok(val),
        Err(_) => {
            eprintln!("{} cannot be represented as a u64", s);
            Err(())
        }
    }
}
