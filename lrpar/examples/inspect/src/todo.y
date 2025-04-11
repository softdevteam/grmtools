%grmtools{yacckind: Original(GenericParseTree)}
%token NAME
%token TODO
%%
Start: %empty | TODO ':' '[' items ']';
items: item | items ',' item;
item: NAME | %empty;
