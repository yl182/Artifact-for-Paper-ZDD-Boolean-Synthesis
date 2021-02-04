{
  open Tptpparser
}
rule token = parse
    "inputformula" { INWFF }
  | "hypothesis" { HYP }
  | "conjecture" { CONJ }
  | "pos" { POS }
  | "box" { BOX }
  | '&' { AND }
  | '|' { OR }
  | ',' { COMMA }
  | '.' { DOT }
  | ':' { COLON }
  | '~' { TILDE }
  | '(' { LP }
  | ')' { RP }
  | "=>" {ARROW}
  | "true" { TRUE }
  | "false" { FALSE }
  | ['r']['0'-'9']+ { REL(int_of_string(
			    String.sub (Lexing.lexeme lexbuf) 1 
					  ( 
					    (String.length (Lexing.lexeme lexbuf))
					    - 
					    1
					  )
			  )) } 
  | ['v']['0'-'9']+ { PROP(int_of_string(
			    String.sub (Lexing.lexeme lexbuf) 1 
					  ( 
					    (String.length (Lexing.lexeme lexbuf))
					    - 
					    1
					  )
			  )) } 
  | (['a'-'z']|['0'-'9']|['A'-'Z'])+ { IDENT }
  | ['%'][^'\n']*['\n'] { token lexbuf }
  | [' ''\t''\n'] {token lexbuf }
  | eof { EOF }
