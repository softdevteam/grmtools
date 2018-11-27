%start Expr
%type u64
%%
Expr: Term 'PLUS' Expr { $1 + $3 }
    | Term { $1 }
    ;

Term: Factor 'MUL' Term { $1 * $3 }
    | Factor { $1 }
    ;

Factor: 'LBRACK' Expr 'RBRACK' { $2 }
      | 'INT' { parse_int($1) }
      ;
%%

fn parse_int(s: &str) -> u64 {
    match s.parse::<u64>() {
    	Ok(val) => val as u64,
        Err(_) => panic!("{} cannot be represented as a u64", s)
    }
}
