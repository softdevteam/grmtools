%token a b
%%
A -> (): B b  {};
C -> (): {};
C -> (): B {};
B: {};