%{
  open Qbfformula
%}

%token <int> INT
%token Q P QBF ZERO EOF A E
%start main
%type <Qbfformula.formula> main
%%

main:
  formula EOF {$1}

formula:
    header allquantifiers clauses { unroll_quant $3 $2 }
  | header clauses { 
	$2
    }

header: 
  P QBF INT INT { () }

allquantifiers:
    existquantifiers { $1 }
  | dimacsquantifiers { $1 }

dimacsquantifiers: 
    dimacsquantifier dimacsquantifiers { $1::$2 }
  | { [] }

dimacsquantifier:
    A qvars { (`Forall,$2) }
  | E qvars { (`Exists,$2) }

existquantifiers:
    quantifiers forallquantifiers { (`Exists,$1)::$2  }
  | { [] }

forallquantifiers: 
    quantifiers existquantifiers { (`Forall,$1)::$2  }
  | { [] }
      
quantifiers:
    Q qvars { $2 } 

qvars:
    INT qvars { $1::$2 }
  | ZERO { [] }

clauses:
    clauses_int { `And($1) }

clauses_int:
    clause clauses_int { $1::$2 }
  | { [] }

clause:
    clause_int { match $1 with
		     [] -> `True
		   | _ -> `Or($1) }

clause_int:
    ZERO { [] }
  | INT clause_int { 
      let f = if ($1 > 0) then `Prop($1) else `Not(`Prop(-$1)) in
		       f::$2
		   }

%%
