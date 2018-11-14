%start Expr
%%
Expr: Term 'PLUS' Expr { add($1, $3) }
    | Term { $1 }
    ;

Term: Factor 'MUL' Term { mul ($1, $3) }
    | Factor { $1 }
    ;

Factor: 'LBRACK' Expr 'RBRACK' { $2 }
      | 'INT' { int($1) }
      ;
%%

type TYPE = u64;

fn int(s: &str) -> TYPE {
    match s.parse::<u64>() {
    	Ok(val) => val as TYPE,
	Err(_) => unreachable!()
    }
}

fn add(arg1: u64, arg2: u64) -> u64 {
    arg1 + arg2
}

fn mul(arg1: u64, arg2: u64) -> u64 {
    arg1 * arg2
}
