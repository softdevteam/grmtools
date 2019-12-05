%start Expr
%avoid_insert "INT"
%%
Expr -> Result<Expr<'input>, ()>:
      Term '+' Expr { Ok(Expr::Add{lhs: Box::new($1?), rhs: Box::new($3?)}) }
    | Term { $1 }
    ;

Term -> Result<Expr<'input>, ()>:
      Factor '*' Term { Ok(Expr::Mul{lhs: Box::new($1?), rhs: Box::new($3?)}) }
    | Factor { $1 }
    ;

Factor -> Result<Expr<'input>, ()>:
      '(' Expr ')' { $2 }
    | 'INT' { Ok(Expr::Number($lexer.lexeme_str(&$1.map_err(|_| ())?))) }
    ;
%%

#[derive(Debug)]
pub enum Expr<'input> {
    Add {
        lhs: Box<Expr<'input>>,
        rhs: Box<Expr<'input>>,
    },
    Mul {
        lhs: Box<Expr<'input>>,
        rhs: Box<Expr<'input>>,
    },
    Number(&'input str)
}
