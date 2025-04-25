%grmtools{
    yacckind: Original(GenericParseTree),
    test_files: "input.txt",
}
%start Expr
%%
Expr: Expr Text | ;

Text: 'TEXT';
