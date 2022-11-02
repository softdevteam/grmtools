%start Expr
%avoid_insert "INT"
%%
Expr: Expr '+' Term
    | Term ;

Term: Term '*' Factor
    | Factor ;

Factor: '(' Expr ')'
      | 'INT';
