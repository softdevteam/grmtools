%%
S -> Result<(), ()>:
    "ANY_CHAR" "WS" {Ok(println!("Any {:?}", $1))}
  | "WS" {Ok(println!("WS {:?}",$1))}
  | {Ok(println!("epsilon"))};
