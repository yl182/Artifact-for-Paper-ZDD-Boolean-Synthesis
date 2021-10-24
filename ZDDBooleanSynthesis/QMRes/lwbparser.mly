%{
  open Kformula
%}

%token <int> PROP
%token AND OR BOX DIA TILDE LP RP ARROW DOUBLEARROW TRUE FALSE EOF
%start main
%type <Kformula.formula> main
%%

main: 
    formula { $1 }

formula: 
    boolean_expression { $1 }
  | rule_expression { $1 }
  | atomic_expression { $1 }

boolean_expression: 
    LP formula ARROW formula RP { Or[ (Not( $2 ) ); $4 ] }
  | LP formula DOUBLEARROW formula RP { And[ Or[ (Not( $2 ) ); $4 ]; Or[ $2; (Not( $4 ) ) ] ] }
  | LP formula AND formula RP { And[ $2; $4 ] }
  | LP formula OR formula RP { Or[ $2; $4 ] }
  | LP TILDE formula RP { Not( $3 ) }

rule_expression: 
    LP BOX formula RP { Modal( ModalOp(Box, 1), $3 ) }
  | LP DIA formula RP { Modal( ModalOp(Diamond, 1), $3 ) }

atomic_expression: 
    PROP { Prop( $1 ) }
  | TRUE { True }
  | FALSE { False } 

