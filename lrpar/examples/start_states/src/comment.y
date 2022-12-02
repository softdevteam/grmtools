%start Expr
%%
Expr: Expr Text | ;

Text: 'TEXT';