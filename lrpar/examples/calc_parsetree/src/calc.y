%start Expr
%avoid_insert "INT"
%%
Expr: Term 'PLUS' Expr
    | Term ;

Term: Factor 'MUL' Term
    | Factor ;

Factor: 'LBRACK' Expr 'RBRACK'
      | 'INT';
