{
  open Dimacsparser
}

rule token = parse
  | 'p' {P}
  | "cnf" {QBF}
  | 'q' {Q}
  | 'a' {A}
  | 'e' {E}
  | ('-'['0'-'9']+)|(['0'-'9']+) {
      let i = int_of_string (Lexing.lexeme lexbuf) in
	if (i = 0) then ZERO else INT(i)
    }
  | 'c'[' ''\t'][^'\n''\r']*['\n''\r'] { token lexbuf }
  | "c\n" { token lexbuf }
  | [' ''\t''\n'] {token lexbuf }
  | '%' { EOF }
  | eof { EOF }
