%start Expr
%%
Expr: Expr Text
    | Text ;

Text: 'TEXT';