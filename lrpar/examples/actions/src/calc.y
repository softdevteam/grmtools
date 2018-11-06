%start Expr
%%
Expr: Term 'PLUS' Expr { add($0, $2) }
    | Term { $0 }
    ;

Term: Factor 'MUL' Term { mul ($0, $2) }
    | Factor { $0 }
    ;

Factor: 'LBRACK' Expr 'RBRACK' { $1 }
      | 'INT' { $0 }
      ;
%%

type TYPE = u64;

fn convert(s: &str) -> TYPE {
    match s.parse::<u64>() {
    	Ok(val) => val as TYPE,
	Err(_) => 0 as TYPE
    }
}

fn add(arg1: u64, arg2: u64) -> u64 {
    arg1 + arg2
}

fn mul(arg1: u64, arg2: u64) -> u64 {
    arg1 * arg2
}
