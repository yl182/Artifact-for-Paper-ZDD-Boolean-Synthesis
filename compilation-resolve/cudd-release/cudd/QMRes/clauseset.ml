open Qbfformula
open Zres
open Options

let make_clause_set f =
  Printf.printf "Building clause set\n";
  flush_all ();
  let cl = ref empty_set in
  let make_clause c =
    let make_lits l =
      let l' = List.map (fun g -> match g with 
			     `Prop(v) -> v
			   | `Not(`Prop(v)) -> (-v)
			   | _ -> raise Bad_formula
			) l in    
	cl := subsumption_free_union (build_clause l') !cl
    in
    match c with
      |	`Or(l) -> make_lits l
      | `Prop(v) -> make_lits [c]
      | `Not(`Prop(v)) -> make_lits [c]
      | _ -> raise Bad_formula
  in
  let _ = match f with
      `And(l) -> let _ = List.map make_clause l in ()
    | `Or(l) -> let _ = make_clause f in ()
    | _ -> raise Bad_formula;
  in
    Printf.printf "Clause set done\n";
    flush_all ();
    !cl

let sort_clauses l = 
  let l' = List.map (List.sort (fun a b -> Pervasives.compare (abs a) (abs b))) l in
  let l'' = List.sort (fun a b -> let head a = match a with [] -> 0 | hd::_ -> hd in Pervasives.compare (head a) (head b)) l' in
    l''
	
let sort_clauses_reordered l ord = 
  let l' = List.map (List.sort (fun a b -> Pervasives.compare ord.((abs a)) ord.((abs b)))) l in
  let l'' = List.sort (fun a b -> 
			 let head a = match a with [] -> 0 | hd::_ -> hd in 
			 let sign a = if a<0 then -1 else if a>0 then 1 else 0 in 
			 let x = Pervasives.compare (sign (head a)) (sign (head b)) in 
			   if x=0 then 
			     Pervasives.compare (x*ord.(abs((head a)))) (x*ord.(abs((head b)))) else x 
		      ) l' in
    l''
  

let make_clause_set_fast f sort_clauses =
  if !quiet_output then () else (
    Printf.printf "Building clause set\n";
    flush_all ();
  );
  let lit_list l = 
    let lit l = 
      match l with
	  `Prop(v) -> v
	| `Not(`Prop(v)) -> -v
	| _ -> (print_string "BAD"; flush_all (); raise Bad_formula)
    in
      List.map lit l
  in
  let formula_to_lit_list f =
    let formula_to_lit_list_int f = 
      match f with
	  `Or(l) -> lit_list l
	| `Prop(v) -> lit_list [f]
	| `Not(`Prop(v)) -> lit_list [f]
	| _ -> (print_string "BAd"; flush_all (); raise Bad_formula)
    in
      match f with
	  `And(l) -> List.map formula_to_lit_list_int l 
	| _ -> (print_string "Bad"; flush_all (); raise Bad_formula)
  in
  let make_clauses l = 
    let rec make_clauses_int2 cl =
      match cl with
	  x::y::tl -> (subsumption_free_union x y)::(make_clauses_int2 tl)
	| [x] -> [x]
	| [] -> []
    in
    let rec make_clauses_int cl = 
      match cl with
	  [] -> []
	| [x] -> [x]
	| _ -> make_clauses_int (make_clauses_int2 cl)
    in 
    let l' = sort_clauses l in
    let _ = if !quiet_output then () else (
      Printf.printf "sorted";
      flush_all ();
    ) in
    let c = List.map build_clause l' in
    let _ = if !quiet_output then () else (
      Printf.printf "built";
      flush_all ();
    ) in
      make_clauses_int c
  in
  let l = formula_to_lit_list f in
  let _ = if !quiet_output then () else (
    Printf.printf "$";
    flush_all ();
  ) in
  let [x] = make_clauses l in
  let _ = if !quiet_output then () else (
    Printf.printf "Clause set done\n";
    flush_all ();
  ) in
    x

let make_clause_set_fast_recursive f = 
  let lit_list l = 
    let lit l = 
      match l with
	  `Prop(v) -> v*2
	| `Not(`Prop(v)) -> v*2+1
	| _ -> (print_string "BAD"; flush_all (); raise Bad_formula)
    in
      List.map lit l
  in
  let formula_to_lit_list f =
    let formula_to_lit_list_int f = 
      match f with
	  `Or(l) -> lit_list l
	| `Prop(v) -> lit_list [f]
	| `Not(`Prop(v)) -> lit_list [f]
	| _ -> (print_string "BAd"; flush_all (); raise Bad_formula)
    in
      match f with
	  `And(l) -> List.map formula_to_lit_list_int l 
	| _ -> (print_string "Bad"; flush_all (); raise Bad_formula)
  in
  let sort_clauses l = 
    let rec compare_list a b = 
      match (a,b) with
	  ([],[]) -> 0
	| ([],hd::tl) -> -1
	| (hd::tl,[]) -> 1
	| (hd::tl,hd'::tl') -> 
	    let r = Pervasives.compare hd hd' in
	      if r = 0 then compare_list tl tl' else r
    in
    let l' = List.map (List.sort Pervasives.compare) l in
    let l'' = List.sort compare_list l' in
    l''
  in
  let rec make_clause_set_int l = 
    let split_clause_list l =
      let rec split_clause_list_int l l' i =
	match l with
	    [] -> (l',[],i)
	  | hd::tl -> 
	    if (List.hd hd)=i then
	      split_clause_list_int tl (l'@[hd]) i
	    else
	      (l',l,i)
      in
	split_clause_list_int l [] (List.hd (List.hd l))
    in
    let strip_top x = List.map List.tl x in
    match l with 
	[] -> empty_set
      | []::_  -> empty_clause
      | _ ->
	  let (a,b,i) = split_clause_list l in
	  let a' = strip_top a in
	  let x = make_clause_set_int a' in
	  let y = make_clause_set_int b in
	    getzdd i x y
  in
    if !quiet_output then () else (
    Printf.printf "Building clause set\n";
    flush_all (););
    let l = formula_to_lit_list f in
    if !quiet_output then () else (
    Printf.printf "$";
    flush_all (););
    let l' = sort_clauses l in
    if !quiet_output then () else (
    Printf.printf "$";
    flush_all (););
    let x = make_clause_set_int l' in
    if !quiet_output then () else (
    Printf.printf "done";
    flush_all (););
      x
