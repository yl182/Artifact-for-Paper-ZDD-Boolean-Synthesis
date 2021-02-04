{
  open Lwbparser
}

rule token = parse
  | "dia" { DIA }
  | "box" { BOX }
  | '&' { AND }
  | 'v' { OR }
  | '~' { TILDE }
  | '(' { LP }
  | ')' { RP }
  | "->" {ARROW}
  | "<->" {DOUBLEARROW}
  | "true" { TRUE }
  | "false" { FALSE }
  | ['p']['0'-'9']+ { PROP(int_of_string(
			    String.sub (Lexing.lexeme lexbuf) 1 
					  ( 
					    (String.length (Lexing.lexeme lexbuf))
					    - 
					    1
					  )
			  )) } 
  | ['%'][^'\n']*['\n'] { token lexbuf }
  | [' ''\t''\n'] {token lexbuf }
  | eof { EOF }
