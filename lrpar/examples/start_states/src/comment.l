%x COMMENT
%%
.                       "TEXT"
<COMMENT,INITIAL>/\*    <+COMMENT>;
<COMMENT>.              ;
<INITIAL,COMMENT>\n             ;
<COMMENT>\*/            <-COMMENT>;
