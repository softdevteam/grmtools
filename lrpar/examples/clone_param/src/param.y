%grmtools {yacckind: Grmtools}
%token Incr Decr
%parse-param val: Rc<RefCell<i64>>
%%
Expr -> () : "INT" Ops {
	*val.borrow_mut() += parse_int($lexer.span_str($1.map_err(|_| "<evaluation aborted>").unwrap().span())).unwrap()
	};
Ops -> (): 
	%empty {}
	| Ops Incr { *val.borrow_mut() += 1; }
	| Ops Decr { *val.borrow_mut() -= 1; };
%%
use std::{ rc::Rc, cell::RefCell, error::Error };

fn parse_int(s: &str) -> Result<i64, Box<dyn Error>> {
    match s.parse::<i64>() {
        Ok(val) => Ok(val),
        Err(_) => {
            Err(Box::from(format!("{} cannot be represented as a i64", s)))
        }
    }
}
