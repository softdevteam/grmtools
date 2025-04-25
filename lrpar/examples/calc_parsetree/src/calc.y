%grmtools{
    yacckind: Original(GenericParseTree),
    test_files: "input.txt",
}
%start Expr
%avoid_insert "INT"
%%
Expr: Expr '+' Term
    | Term ;

Term: Term '*' Factor
    | Factor ;

Factor: '(' Expr ')'
      | 'INT';
