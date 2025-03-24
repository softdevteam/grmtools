%grmtools{yacckind: Grmtools}
%%
word_seq -> Vec<String>
    : "word" {vec![$lexer.span_str($1.as_ref().unwrap().span()).to_string()]
    }
    | word_seq "," "word" {
        let w: String = $lexer.span_str($3.as_ref().unwrap().span()).to_string();
        $1.push(w);
        $1
    }
    ;
%%
