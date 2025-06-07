%grmtools {
    yacckind: Grmtools,
    test_files: "input*.txt",
}
%start Expr
%avoid_insert "INT"
%expect-unused Unmatched "UNMATCHED"
%parse-generics 'ast
%parse-param arena: &'ast Bump
%%
Expr -> Result<Expr<'ast>, ()>:
      Expr '+' Term {
        Ok(Expr::Add{ span: $span, lhs: arena.alloc($1?), rhs: arena.alloc($3?) })
      }
    | Term { $1 }
    ;

Term -> Result<Expr<'ast>, ()>:
      Term '*' Factor {
        Ok(Expr::Mul{ span: $span, lhs: arena.alloc($1?), rhs: arena.alloc($3?) })
      }
    | Factor { $1 }
    ;

Factor -> Result<Expr<'ast>, ()>:
      '(' Expr ')' { $2 }
    | 'INT' { Ok(Expr::Number{ span: $span }) }
    ;

Unmatched -> ():
      "UNMATCHED" { }
    ;
%%

use cfgrammar::Span;
use bumpalo::Bump;

#[derive(Debug)]
pub enum Expr<'ast> {
    Add {
        span: Span,
        lhs: &'ast Expr<'ast>,
        rhs: &'ast Expr<'ast>,
    },
    Mul {
        span: Span,
        lhs: &'ast Expr<'ast>,
        rhs: &'ast Expr<'ast>,
    },
    Number {
        span: Span
    }
}
