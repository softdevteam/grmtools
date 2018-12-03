%start Expr
%type Result<u64, ()>
%%
Expr: Term 'PLUS' Expr { Ok($1? + $3?) }
    | Term { $1 }
    ;

Term: Factor 'MUL' Term { Ok($1? * $3?) }
    | Factor { $1 }
    ;

Factor: 'LBRACK' Expr 'RBRACK' { $2 }
      | 'INT' {
            let l = $1.map_err(|_| ())?;
            match $lexer.lexeme_str(&l).parse::<u64>() {
                Ok(v) => Ok(v),
                Err(_) => {
                    let (_, col) = $lexer.offset_line_col(l.start());
                    eprintln!("Error at column {}: '{}' cannot be represented as a u64",
                              col,
                              $lexer.lexeme_str(&l));
                    Err(())
                }
            }
        }
      ;
