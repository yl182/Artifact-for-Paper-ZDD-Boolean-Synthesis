%{
  open Kformula
%}

%token <int> REL PROP
%token AND OR BOX POS TILDE LP RP ARROW TRUE FALSE COMMA COLON DOT HYP CONJ TRUE FALSE IDENT INWFF EOF
%start main
%type <Kformula.formula> main
%%

formlist :
    form { $1 }
    | form AND formlist { And( [$1; $3] ) }
    | form OR formlist { Or( [$1; $3] ) }
    | form ARROW formlist { Or( [Not($1); $3] ) }

complexform :
    LP formlist RP { $2 }
    | LP BOX REL COLON form RP { Modal ( ModalOp(Box, $3), $5 ) }
    | LP POS REL COLON form RP { Modal ( ModalOp(Diamond, $3), $5 ) }

form :
    TRUE { True }
    | FALSE { False }
    | PROP { Prop( $1 ) }
    | TILDE form { Not( $2 ) }
    | complexform { $1 }

decl :
    LP IDENT COMMA HYP COMMA form RP DOT { $6 }
    | LP IDENT COMMA CONJ COMMA form RP DOT { Not( $6 ) }

decllist :
    INWFF decl decllist { And( [$2; $3] ) }
    | INWFF decl { $2 }

main :
    decllist EOF { $1 }




