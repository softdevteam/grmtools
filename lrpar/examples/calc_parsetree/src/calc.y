%start Expr
%avoid_insert "INT"
%%
Expr: Factor 'PLUS' Expr
    | Factor ;

Factor: Term 'MUL' Factor
    | Term ;

Term: 'LBRACK' Expr 'RBRACK'
      | 'INT';
