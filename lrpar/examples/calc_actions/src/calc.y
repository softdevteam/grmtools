%start Expr
%avoid_insert "INT"
%%
Expr -> Result<u64, Box<dyn Error>>:
      Expr '+' Term { Ok($1?.checked_add($3?)
                            .ok_or_else(|| Box::<dyn Error>::from("Overflow detected."))?)
                    }
    | Term { $1 }
    ;

Term -> Result<u64, Box<dyn Error>>:
      Term '*' Factor { Ok($1?.checked_mul($3?)
                              .ok_or_else(|| Box::<dyn Error>::from("Overflow detected."))?)
                      }
    | Factor { $1 }
    ;

Factor -> Result<u64, Box<dyn Error>>:
      '(' Expr ')' { $2 }
    | 'INT'
      {
          parse_int($lexer.span_str($1.map_err(|_| "<evaluation aborted>")?.span()))
      }
    ;
%%
// Any imports here are in scope for all the grammar actions above.

use std::error::Error;

fn parse_int(s: &str) -> Result<u64, Box<dyn Error>> {
    match s.parse::<u64>() {
        Ok(val) => Ok(val),
        Err(_) => {
            Err(Box::from(format!("{} cannot be represented as a u64", s)))
        }
    }
}
