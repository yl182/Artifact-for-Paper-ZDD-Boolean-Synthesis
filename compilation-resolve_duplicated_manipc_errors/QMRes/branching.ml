open Common
open Cudd
open Zres
open Options

exception Cannot_choose_var

type branch_vars = (bool * int list) list

class type ['t] abstract_branching = 
object
  method branch: 't -> branch_vars -> int -> 't list * branch_vars * bool * int
end

let rec app_lit s u =
  if u = empty_clause then s 
  else 
    let x = zdd_var u in
    let i = x/2 in
    let (st,sf,sn) = split_subset i s in
    let s' = 
      if (i mod 2) = 0 then
	subsumption_free_union sf sn
      else
	subsumption_free_union st sn
    in
      app_lit s' (zdd_t u)

let rec simp_unit_pure s = 
  let u' = if !use_unit then 
    if !is_qbf then
      find_existential_unit_literals s 
    else
      find_unit_literals s
  else
    empty_clause 
  in
  let u'' = if !use_pure then
    find_qbf_pure_literals s
  else
    empty_clause
  in
  let u = clause_distribution u' u'' in
    if u = empty_clause then
      s
    else (
      if !debug_branching > 0 then (
	Printf.printf "Simplifying %d %d\n" (clause_set_size u') (clause_set_size u'');
	flush_all ();
      );
      simp_unit_pure (apply_literals s u)
(*      simp_unit_pure (app_lit s u)*)
    )

class zr_branching = 
object (self:clause_set #abstract_branching)
  method branch s bv sv =
    let clause_set_split_size_ratio v s =
      let size s = let ss = clause_set_size s in
	if ss = -1 or ss = 0 then 1.0 else (float_of_int (ss+1)) 
      in
      let size_orig = size s in
      let (t,f,n) = split_subset v s in
      let sizet = size t in
      let sizef = size f in
      let sizen = size n in
	if !debug_branching > 1 then
	  Printf.printf "Splitting sizes is %f %f %f:%f " sizet sizef sizen size_orig;
	size_orig/.(sizet+.sizef+.0.3*.sizen)
    in
    let rec choose_branch_var_int (bestsr,bestv) vl s =
      match vl with
	  [] -> (bestsr,bestv)
	| hd::tl -> 
	    let srnew = (clause_set_split_size_ratio hd s) in
	      if !debug_branching > 1 then
		Printf.printf "Instecting splitting var %d score = %f\n" hd srnew;
	      if (srnew < bestsr) then 
		if (srnew < !Options.splitting_score_threshold) then
		  (srnew, hd)
		else
		choose_branch_var_int (srnew, hd) tl s
	      else
		choose_branch_var_int (bestsr, bestv) tl s
    in
    let (is_exist,vl)::tl = bv in
    let _ =  if !debug_branching > 1 then (
	print_string "choosing from ";
	print_int_list vl ;
	print_string "\n";
    ) in
    let (sr,v) = if List.mem sv vl then
      (0.0, sv) 
    else
      let (_,_,n) = split_subset sv s in
      let s' = subtract s n in
	choose_branch_var_int (max_float, -1) vl s' 
    in
      if v = -1 then
	raise Cannot_choose_var
      else
	let vl' = erase_from_list v vl in
	let bv' = if vl'=[] then tl else (is_exist,vl')::tl in
	let (t,f,n) = split_subset v s in
	  Printf.printf "branching\n";
	  flush_all ();
	let t' = subsumption_free_union t n in
	let t'' = simp_unit_pure t' in
	let f' = subsumption_free_union f n in
	let f'' = simp_unit_pure f' in
	  if !debug_branching > 0 then
	    Printf.printf "Splitted var=%d score=%f size %d %d" v sr (clause_set_size t') (clause_set_size f');
	  ([t'';f''], bv', is_exist, v)  
end

let pos s v =
  bdd_and (bdd_var v) s

let neg s v =
  bdd_and (bdd_not (bdd_var v)) s

class bdd_branching = 
object (self:(bdd * clause_set) #abstract_branching)
  method branch (b,s) bv sv = 
    let rec choose_branch_var_int (bestsr,bestv) vl s =
      match vl with
	  [] -> (bestsr,bestv)
	| hd::tl -> 
	    let srnew = (float_of_int ((bdd_size (pos s hd))+(bdd_size (neg s hd))))/.(float_of_int (bdd_size s)) in
	      if !debug_branching > 1 then
		Printf.printf "Instecting splitting var %d score = %f\n" hd srnew;
		if (srnew < bestsr) then 
		  if (srnew < !Options.splitting_score_threshold) then
		    (srnew, hd)
		  else
		    choose_branch_var_int (srnew, hd) tl s
		else
		  choose_branch_var_int (bestsr, bestv) tl s
    in
    let (is_exist,vl)::tl = bv in
    let _ =  if !debug_branching > 1 then (
	print_string "choosing from ";
	print_int_list vl ;
	print_string "\n";
    ) in
    let (sr,v) = if List.mem sv vl then
      (0.0, sv) 
    else
      choose_branch_var_int (max_float, -1) vl b 
    in
      if v = -1 then
	raise Cannot_choose_var
      else
	let vl' = erase_from_list v vl in
	let bv' = if vl'=[] then tl else (is_exist,vl')::tl in
	let t = pos b v in
	let f = neg b v in
	let (t',f',n) = split_subset v s in
	let t'' = subsumption_free_union t' n in
	let f'' = subsumption_free_union f' n in
	  Printf.printf "branching\n";
	  flush_all ();
	  if !debug_branching > 0 then
	    Printf.printf "Splitted var=%d score=%f size %d %d" v sr (bdd_size t) (bdd_size f);
	  ([(t,t'');(f,f'')], bv', is_exist, v)
end

class zr_branching2 = 
object (self:clause_set #abstract_branching)
  method branch s bv sv =
    let (is_exist,vl)::tl = bv in
    let _ =  if !debug_branching > 1 then (
	print_string "choosing from ";
	print_int_list vl ;
	print_string "\n";
    ) in
    let (sr,v) = if List.mem sv vl then
      (0.0, sv) 
    else
      match vl with
	  hd::tl -> (0.0, hd)
	| _ -> (0.0, -1)
    in
      if v = -1 then
	raise Cannot_choose_var
      else
	let _::vl' = vl in
	let bv' = if vl'=[] then tl else (is_exist,vl')::tl in
	let (t,f,n) = split_subset v s in
	  Printf.printf "branching\n";
	  flush_all ();
	let t' = subsumption_free_union t n in
	let t'' = simp_unit_pure t' in
	let f' = subsumption_free_union f n in
	let f'' = simp_unit_pure f' in
	  if !debug_branching > 0 then
	    Printf.printf "Splitted var=%d score=%f size %d %d" v sr (clause_set_size t') (clause_set_size f');
	  ([t'';f''], bv', is_exist, v)  
end



