%start Expr
%type MYTYPE
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

type MYTYPE = u64;

fn int(s: &str) -> MYTYPE {
    match s.parse::<u64>() {
    	Ok(val) => val as MYTYPE,
	Err(_) => unreachable!()
    }
}

fn add(arg1: u64, arg2: u64) -> u64 {
    arg1 + arg2
}

fn mul(arg1: u64, arg2: u64) -> u64 {
    arg1 * arg2
}
