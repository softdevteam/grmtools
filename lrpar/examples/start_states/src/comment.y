%grmtools{yacckind Original(GenericParseTree)}
%start Expr
%%
Expr: Expr Text | ;

Text: 'TEXT';
