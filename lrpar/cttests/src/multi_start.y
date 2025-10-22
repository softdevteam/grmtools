%grmtools{yacckind: Grmtools}
%start AStart
%token A B C
%%

AStart -> ()
 : A ':' BStart ';' {}
 ;

BStart -> () 
 : B ',' C {}
 | C ',' B {}
 ;
