%start Expr
%avoid_insert "INT"
%%
Expr -> Result<Expr<'input>, ()>:
      Term '+' Expr { Ok(Expr::Add{span: $span, lhs: Box::new($1?), rhs: Box::new($3?)}) }
    | Term { $1 }
    ;

Term -> Result<Expr<'input>, ()>:
      Factor '*' Term { Ok(Expr::Mul{span: $span, lhs: Box::new($1?), rhs: Box::new($3?)}) }
    | Factor { $1 }
    ;

Factor -> Result<Expr<'input>, ()>:
      '(' Expr ')' { $2 }
    | 'INT' { Ok(Expr::Number{span: $span, int: $lexer.lexeme_str(&$1.map_err(|_| ())?) }) }
    ;
%%

use lrpar::Span;

#[derive(Debug)]
pub enum Expr<'input> {
    Add {
        span: Span,
        lhs: Box<Expr<'input>>,
        rhs: Box<Expr<'input>>,
    },
    Mul {
        span: Span,
        lhs: Box<Expr<'input>>,
        rhs: Box<Expr<'input>>,
    },
    Number {
        span: Span,
        int: &'input str
    }
}
