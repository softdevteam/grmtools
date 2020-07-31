%start Expr
%avoid_insert "INT"
%%
Expr: Expr 'PLUS' Term
    | Term ;

Term: Term 'MUL' Factor
    | Factor ;

Factor: 'LBRACK' Expr 'RBRACK'
      | 'INT';
