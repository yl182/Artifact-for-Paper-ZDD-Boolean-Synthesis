open Kformula

let parse_tptp name = 
  let inf = open_in name in
  let lexbuf = Lexing.from_channel inf in
  let result = Tptpparser.main Tptplex.token lexbuf in
    result

let parse_lwb name = 
  let inf = open_in name in
  let lexbuf = Lexing.from_channel inf in
  let result = Lwbparser.main Lwblex.token lexbuf in
    result

let load_k name =
  try
    parse_tptp name
  with e ->
      try 
	parse_lwb name
      with e ->
	  raise e

let random size props mtop bbias abias = 
  let rec random_int size props mtop = (
    match size with
	1 -> 
	  if (Random.int 2) = 0 then
	    Prop(Random.int props)
	  else
	    Not(Prop(Random.int props))
      | 2 -> 
	  if (mtop = 0.0) then
	    random_int 1 props mtop
	  else
	    if (Random.float 1.0) < bbias then
	      Modal(ModalOp(Box, 0), random_int 1 props mtop)
	    else
	      Modal(ModalOp(Diamond, 0), random_int 1 props mtop)
      | _ when size > 2 -> (
	  let choice = Random.float 1.0 in
	    if (choice < mtop *. bbias) then
	      Modal(ModalOp(Box, 0), random_int (size - 1) props mtop)
	    else if (choice < mtop) then
	      Modal(ModalOp(Diamond, 0), random_int (size - 1) props mtop)
	    else
	      let choice' = (choice -. mtop) /. mtop in
	      let cutsize = (Random.int (size - 2)) + 1 in
	      let l = random_int cutsize props mtop in
	      let r = random_int (size - cutsize - 1) props mtop in
		if (choice' < abias) then
		  And([l;r])
		else 
		  Or([l;r])
	)
      | _ -> Prop(0)
		    
  ) in
    Random.self_init ();
    random_int size props mtop
		  
let random_n size props mtop bbias abias = 
  let rec random_n_int size props mtop = (
    match size with
	1 -> 
	  if (Random.int 2) = 0 then
	    Prop(Random.int props)
	  else
	    Not(Prop(Random.int props))
      | 2 -> 
	  if (mtop = 0.0) then
	    random_n_int 1 props mtop
	  else
	    if (Random.float 1.0) < bbias then
	      Modal(ModalOp(Box, 0), random_n_int 1 props mtop)
	    else
	      Modal(ModalOp(Diamond, 0), random_n_int 1 props mtop)
      | _ when size > 2 -> (
	  let choice = Random.float 1.0 in
	    if (choice < mtop *. bbias) then
	      Modal(ModalOp(Box, 0), random_n_int (size - 1) props mtop)
	    else if (choice < mtop) then
	      Modal(ModalOp(Diamond, 0), random_n_int (size - 1) props mtop)
	    else
	      let branches = (Random.int 30) + 2 in
	      let branches = (if size < branches then
				size
			      else
				branches
			     ) in
	      let choice' = (choice -. mtop) /. mtop in
	      let rec build_rand_list size n =
		match size with
		    0 -> []
		  | _ ->	 (if (n = 0) then 0 else (Random.int n))
		      :: build_rand_list (size-1) n in
	      let rl = build_rand_list (branches - 1) (size - branches) in
	      let rl' = List.sort Pervasives.compare ( (size - branches) :: rl) in
	      let rec build_form rl init =
		match rl with
		    [] -> []
		  | hd::tl -> (random_n_int (hd-init+1) props mtop) :: (build_form tl hd) in
	      let l = build_form rl' 0 in
		if (choice' < abias) then
		  And(l)
		else 
		  Or(l)
	)
      | _ -> Prop(0)
		    
  ) in
    Random.self_init ();
    random_n_int size props mtop

let random_cnf l n c m d p =
  let random_lit () = 
    if (Random.int 2) = 0 then
      Prop(Random.int n)
    else
      Not(Prop(Random.int n))
  and random_int_of_float x = 
    let x' = int_of_float x in
    let x'' = float_of_int x' in
      if (Random.float 1.0) > (x-.x'') then x' else x'+1
  in
  let rec random_modal_atom d =
    let b = Random.int m in
    let x = Modal(ModalOp(Box, b), random_clause (d-1)) in
      if (Random.int 2) = 0 then x else Not(x)
  and random_clause_list l =
    match l with
	0 -> []
      | _ -> (random_clause d) :: (random_clause_list (l-1))
  and random_clause d = 
    let rec gen_atom_list proc size = 
      match size with
	  0 -> []
	| _ -> (proc ()) :: gen_atom_list proc (size-1) in
    let rec trival_clause cl = 
      let rec check_trival l c =
	match c with
	    [] -> false
	  | hd::tl -> if ((l=hd)||(Not(l)=hd)||(l=Not(hd))) then
	      true
	    else
	      check_trival l tl
      in
      match cl with
	  [] -> false
	| hd::tl -> if (check_trival hd tl) then
	    true
	  else
	    trival_clause tl
    in
    let atoms = random_int_of_float c in
    let prop_atoms = random_int_of_float ((float_of_int atoms) *. p) in
    let prop_atoms' = if d = 0 then atoms else prop_atoms in
    let modal_atoms = atoms - prop_atoms' in
    let lits = (gen_atom_list random_lit prop_atoms') @ (gen_atom_list (fun () -> random_modal_atom d) modal_atoms) in
    let clause = Or(lits) in
      if (trival_clause lits) then
	random_clause d
      else
	clause
  in
    And(random_clause_list (int_of_float (l*.(float_of_int n))))
      

let rec print_lwb form =
  match form with
      True -> print_string "true"
    | False -> print_string "false"
    | Prop(i) -> print_string "p"; print_int i
    | Not(f) -> print_string "(~"; print_lwb f; print_string ")"
    | Modal(ModalOp(Diamond, i), f) -> print_string "(dia "; print_lwb f; print_string ")";
    | Modal(ModalOp(Box, i), f) -> print_string "(box "; print_lwb f; print_string ")";
    | And( l ) -> print_and l
    | Or( l ) -> print_or l
    | _ -> ()
and print_and l =
  match l with
      [f1;f2] -> print_string "("; print_lwb f1; print_string " & "; print_lwb f2; print_string ")"
    | hd :: tl -> print_string "("; print_lwb hd; print_string " & "; print_and tl; print_string ")"
    | _ -> ()
and print_or l =
  match l with
      [f1;f2] -> print_string "("; print_lwb f1; print_string " v "; print_lwb f2; print_string ")"
    | hd :: tl -> print_string "("; print_lwb hd; print_string " v "; print_or tl; print_string ")"
    | _ -> ()

let rec toplev form = 
  match form with
      True -> True
    | False -> False
    | Prop(i) -> Prop(i)
    | Not(f) -> Not(toplev f)
    | Modal(m, f) -> ( 
	match m with
	    ModalOp(Diamond,i) -> Prop(100+i)
	  | ModalOp(Box,i) -> Prop(200+i)
      )
    | And( l ) -> And( List.map toplev l )
    | Or( l ) -> Or( List.map toplev l )
    | _ -> Invalid

let rec size form = 
  match form with 
      True -> 1
    | False -> 1
    | Prop(i) -> 1
    | Not(f) -> size f
    | Modal(m, f) -> (size f) + 1
    | And( l ) -> (size_list l) + 1
    | Or( l ) -> (size_list l) + 1
    | _ -> 0
and size_list l =
  match l with
      [] -> 0
    | hd :: tl -> (size hd) + (size_list tl)

let rec flatten form = 
  match form with
      True -> True
    | False -> False
    | Prop(i) -> Prop(i)
    | Not(f) -> Not(flatten f)
    | Modal(m, f) -> Modal(m, flatten f)
    | And( [] ) -> True
    | Or( [] ) -> False
    | And( [f] ) -> f
    | Or( [f] ) -> f
    | And( l ) -> And ( flatten_and (List.map flatten l) )
    | Or( l ) -> Or ( flatten_or (List.map flatten l) )
    | _ -> Invalid
and flatten_and l =
  let is_and f = (
    match f with
	And( l ) -> true
      | _ -> false
  ) in
  let strip_and f = (
    match f with
	And( l ) -> l
      | _ -> []
  ) in
    flatten_op is_and l strip_and
and flatten_or l =
  let is_or f = (
    match f with
	Or( l ) -> true
      | _ -> false
  ) in
  let strip_or f = (
    match f with
	Or( l ) -> l
      | _ -> []
  ) in
    flatten_op is_or l strip_or
and flatten_op pred l strip =
  let (l1, l2) = List.partition pred l in
    match l1 with
	[] -> l2
      | _ -> List.rev_append l2 (flatten_op pred (List.concat (List.map strip l1)) strip)

let rec opt_prop form = 
  match form with
      Modal(m, f) -> opt_modal_prop (Modal(m, opt_prop f))
    | And( l ) -> (
	let l2 = List.map opt_prop l in
	let l3 = simplify_list_and l2 in
	let (t,l4) = simplify_list_not l3 in
	  if (t) then
	    False
	  else
	    match l4 with
		[f] -> f
	      | _ -> And( l4 )
      )
    | Or( l ) -> (
	let l2 = List.map opt_prop l in
	let l3 = simplify_list_or l2 in
	let (t, l4) = simplify_list_not l3 in
	  if (t) then
	    True
	  else
	    match l4 with
		[f] -> f
	      | _ -> Or( l4 )
      )
    | _ -> form
and opt_modal_prop f = 
  match f with
      Modal(ModalOp(Box, i), True) -> True
    | Modal(ModalOp(Diamond, i), False) -> False
    | _ -> f
and simplify_list_and l =
  if List.mem False l
  then [False]
  else let l2 = List.filter (function True -> false | _ -> true) l in
    match l2 with
	[] -> [True]
      | _ -> l2
and simplify_list_or l =
  if List.mem True l
  then [True]
  else let l2 = List.filter (function False -> false | _ -> true) l in
    match l2 with
	[] -> [False]
      | _ -> l2
and simplify_list_not l = 
  let (p,n) = List.partition is_not l in
  let n' = List.map strip_not n in
  let ps = to_set p in
  let ns = to_set n' in
  let common = FormulaSet.inter ps ns in
    if (not(FormulaSet.is_empty common)) then 
      let ps' = FormulaSet.diff ps common in
      let ns' = FormulaSet.diff ns common in
      let pp = FormulaSet.elements ps' in
      let nn = FormulaSet.elements ns' in
      let nn' = List.map (fun f -> Not(f)) nn in
      let l' = pp @ nn' in
	(true, l')
    else
      (false, l)

let rec opt_modal form =
  match form with
      True -> True
    | False -> False
    | Prop(i) -> Prop(i)
    | Not(f) -> Not(opt_modal f)
    | Modal(m, f) -> Modal(m, opt_modal f)
    | Or( l ) -> Or( opt_diamond_or 1 (List.map opt_modal l) )
    | And( l ) -> And( opt_box_and 1 (List.map opt_modal l) )
    | _ -> Invalid
and opt_box_and i l =
  let is_box i f = (
    match f with
	Modal(ModalOp(Box, i), f) -> true
      | _ -> false
  ) in
  let (l1, l2) = List.partition (is_box i) l in
    match l1 with
	[] -> l2
      | [f] -> f :: l2
      | _ -> let strip_box f = (
	  match f with
	      Modal(ModalOp(Box, i) , f) -> f
	    | _ -> Invalid
	) in
	  Modal(ModalOp(Box, i), And( List.map strip_box l1 )) :: l2 
and opt_diamond_or i l =
  let is_diamond i f = (
    match f with
	Modal(ModalOp(Diamond, i), f) -> true
      | _ -> false
  ) in
  let (l1, l2) = List.partition (is_diamond i) l in
    match l1 with
	[] -> l2
      | [f] -> f :: l2
      | _ -> let strip_diamond f = (
	  match f with
	      Modal(ModalOp(Diamond, i) , f) -> f
	    | _ -> Invalid
	) in
	  Modal(ModalOp(Diamond, i), Or( List.map strip_diamond l1 )) :: l2 

let rec nnf form = 
  match form with
      True -> True
    | False -> False
    | Prop(i) -> Prop(i)
    | Not(Prop(i)) -> Not(Prop(i))
    | Not(f) -> neg f
    | And( l ) -> And ( List.map nnf l )
    | Or( l ) -> Or ( List.map nnf l )
    | Modal(m,f) -> Modal(m, nnf f)
    | _ -> Invalid
and neg form =
  match form with
      True -> False
    | False -> True
    | Prop(i) -> Not(Prop(i))
    | And( l ) -> Or( List.map neg l )
    | Or( l ) -> And( List.map neg l )
    | Not(f) -> nnf f
    | Modal(ModalOp(Box, i), f) -> Modal(ModalOp(Diamond, i), neg f)
    | Modal(ModalOp(Diamond, i), f) -> Modal(ModalOp(Box, i), neg f)
    | _ -> Invalid
and bnf form = 
  match form with
      True | False | Prop(_) | Not(Prop(_)) | Modal(ModalOp(Box, _), _) -> form
    | And( l ) -> And( List.map bnf l )
    | Or( l ) -> Or( List.map bnf l )
    | Modal(ModalOp(Diamond, i), f) -> Not(Modal(ModalOp(Box, i), neg_bnf f))
    | Not(f) -> neg_bnf f
    | _ -> Invalid
and neg_bnf form =
  match form with
      True -> False
    | False -> True
    | Prop(i) -> Not(Prop(i))
    | And( l ) -> Or( List.map neg_bnf l )
    | Or( l ) -> And( List.map neg_bnf l )
    | Not(f) -> bnf f
    | Modal(ModalOp(Box, i), f) -> Not(Modal(ModalOp(Box, i), bnf f))
    | Modal(ModalOp(Diamond, i), f) -> Modal(ModalOp(Box, i), neg_bnf f)
    | _ -> Invalid

let rec map_new_prop_for_each_level level maxprop form =
  match form with
      Prop(i) -> Prop( level * maxprop + i )
    | And( l ) -> And( List.map (map_new_prop_for_each_level level maxprop) l )
    | Or( l ) -> Or( List.map (map_new_prop_for_each_level level maxprop) l )
    | Modal(m, f) -> Modal(m, (map_new_prop_for_each_level (level+1) maxprop f) )
    | Not(f) -> Not(map_new_prop_for_each_level level maxprop f)
    | _ -> form

let rec unmap_prop_levels maxprop form =
  match form with
      Prop(i) -> Prop( i mod maxprop )
    | And( l ) -> And( List.map (unmap_prop_levels maxprop) l )
    | Or( l ) -> Or( List.map (unmap_prop_levels maxprop) l )
    | Modal(m, f) -> Modal(m, (unmap_prop_levels maxprop f) )
    | Not(f) -> Not(unmap_prop_levels maxprop f)
    | _ -> form

let rec propositions form = 
  match form with
      True -> 0
    | False -> 0
    | Prop(i) -> i + 1
    | Not(f) -> propositions f
    | And( l ) -> List.fold_left max 0 (List.map propositions l)
    | Or( l ) -> List.fold_left max 0 (List.map propositions l)
    | Modal(m, f) -> propositions f
    | _ -> 0

module Int =
  struct
    type t = int
    let compare = Pervasives.compare
  end
module IntSet = Set.Make(Int)

let rec pos_occur_prop form = 
  match form with
      Prop(i) -> IntSet.singleton i
    | Not(Prop(i)) -> IntSet.empty
    | And( l ) -> List.fold_left IntSet.union IntSet.empty ( List.map pos_occur_prop l )
    | Or( l ) -> List.fold_left IntSet.union IntSet.empty ( List.map pos_occur_prop l )
    | Modal(m, f) -> pos_occur_prop f
    | _ -> IntSet.empty
and neg_occur_prop form = 
  match form with
      Prop(i) -> IntSet.empty
    | Not(Prop(i)) -> IntSet.singleton i
    | And( l ) -> List.fold_left IntSet.union IntSet.empty ( List.map neg_occur_prop l )
    | Or( l ) -> List.fold_left IntSet.union IntSet.empty ( List.map neg_occur_prop l )
    | Modal(m, f) -> neg_occur_prop f
    | _ -> IntSet.empty

let rec map_prop_true propset form = 
  match form with
      Prop(i) -> if (IntSet.mem i propset) then True else form
    | Not(f) -> form
    | And( l ) -> And( List.map (map_prop_true propset) l )
    | Or( l ) -> Or( List.map (map_prop_true propset) l )
    | Modal(m, f) -> Modal(m, map_prop_true propset f)
    | _ -> form
and map_prop_false propset form = 
  match form with
      Prop(i) -> form
    | Not(Prop(i)) -> if (IntSet.mem i propset) then True else form
    | And( l ) -> And( List.map (map_prop_false propset) l )
    | Or( l ) -> Or( List.map (map_prop_false propset) l )
    | Modal(m, f) -> Modal(m, map_prop_false propset f)
    | _ -> form

let rec opt_single_occur_prop form = 
  let pos_occur = pos_occur_prop form in
  let neg_occur = neg_occur_prop form in
  let occured_prop = IntSet.inter pos_occur neg_occur in
  let only_pos_prop = IntSet.diff pos_occur occured_prop in
  let only_neg_prop = IntSet.diff neg_occur occured_prop in
  let form1 = map_prop_true only_pos_prop form in
  let form2 = map_prop_false only_neg_prop form1 in
    opt_prop form2







