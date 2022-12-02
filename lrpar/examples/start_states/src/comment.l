%x COMMENT
%%
.                       "TEXT"
<COMMENT,INITIAL>/\*    <+COMMENT>;
<COMMENT>.              ;
<COMMENT>\n             ;
<COMMENT>\*/            <-COMMENT>;
