open Common
open Cudd

type clause_set

external init_zres : unit -> unit = "init_zres"

let _ = init_zres ()

external set_quantifier_map : int array -> unit = "set_quantifier_map"

external set_no_quantification : unit -> unit = "set_no_quantification"

external build_clause : int list -> clause_set = "build_clause"
external add_literal : int -> clause_set -> clause_set = "add_lit"
external subsumption_free_union : clause_set -> clause_set -> clause_set = "sub_free_union"
external split_subset : int -> clause_set -> clause_set * clause_set * clause_set = "split_subset"
external subtract: clause_set -> clause_set -> clause_set = "clause_subtraction"
external print_clauses: clause_set -> unit = "print_clauses_ml"

external bddquant: clause_set -> bdd = "clause_set_to_bdd"
external bddquantnew: clause_set -> bdd = "clause_set_to_bdd_quant_new"
external bddquantnext: clause_set -> bdd = "clause_set_to_bdd_nextbucket"
external bddquantinv: clause_set -> bdd = "clause_set_to_bdd_quant"
external bddnoquant: clause_set -> bdd = "clause_set_to_bdd_noquant"
external bddallquant: clause_set -> bdd = "clause_set_to_bdd_allquant"
external bddallquantbed: clause_set -> bdd = "clause_set_to_bdd_bed"
external cnf2dnf: clause_set -> int -> bdd = "cnf_to_dnf"
external bdd2clauseset: bdd -> clause_set = "bdd_to_clause_set"
external bddchooseclauseset: bdd -> bdd -> clause_set = "bdd_choose_clause_set"

external zddquant: clause_set -> clause_set = "clause_set_quant"

external invertbdd: unit -> unit = "invert_bdd_order"
external setbddvars: int -> unit = "set_num_vars"

external change: clause_set -> int -> clause_set = "clause_set_change"
external getzdd: int -> clause_set -> clause_set -> clause_set = "clause_set_getzdd"

external zdd_var: clause_set -> int = "zdd_var"
external zdd_t: clause_set -> clause_set = "zdd_t"
external zdd_e: clause_set -> clause_set = "zdd_e"

external print_active_vars: unit -> unit = "print_active_vars"

external shuffleheap : int list -> unit = "dd_shuffle_heap"

external clause_set_size : clause_set -> int = "clause_set_size"
external clause_set_clauses : clause_set -> int = "clause_set_clauses"

external find_unit_literals : clause_set -> clause_set = "find_unit_lits"
external find_existential_unit_literals : clause_set -> clause_set = "find_existential_unit_lits"
external apply_literals : clause_set -> clause_set -> clause_set = "apply_lits"
external apply_literals_bounded : clause_set -> clause_set -> int -> clause_set = "apply_lits_bounded"
external bound_cube : clause_set -> int -> clause_set = "bound_cube"

external get_support : clause_set -> bdd = "get_support"
external get_support_zdd : clause_set -> clause_set = "get_support_z"

external filter_tautology : clause_set -> clause_set = "filter_taut"

external unit_prop : clause_set -> clause_set = "unit_prop"

external remove_universal_arbitary : clause_set -> clause_set = "remove_univ_arb"
external remove_universal_exist_before_univ: clause_set -> clause_set = "remove_univ_exist_before_univ"

external qbf_pure_adjust: clause_set -> clause_set = "qbf_pure_adjust"

external make_all_assignments: int -> int -> clause_set = "make_all_assignments"
external remove_unwitnessed_assignments: clause_set -> clause_set -> clause_set = "remove_unwit_assignments"

let bddsplit b = 
  let _ = Printf.printf "orig size = %d " (bdd_size b) in
  let _ = flush_all () in
  let b' = bdd_overapprox b (bdd_total_vars ()) in
  let _ = Printf.printf "approx done size = %d " (bdd_size b') in
  let _ = flush_all () in
  let b'' = bdd_diff b' b in
  let s = bddchooseclauseset b (bdd_not b'') in
  let _ = Printf.printf "splitted size = b(%d), z(%d) \n" (bdd_size b') (clause_set_size s) in
    (b', s)

let true_subset i s =
  let (s',_,_) = split_subset i s in
    s'
let false_subset i s =
  let (_,s',_) = split_subset i s in
    s'
let donotcare_subset i s =
  let (_,_,s') = split_subset i s in
    s'

let universal_abstract v s = 
  let (t,f,n) = split_subset v s in
    subsumption_free_union (subsumption_free_union t f) n

let debug_dump = true

external donotcare_cube : clause_set -> clause_set -> clause_set = "donotcare_cube"
let rec donotcare_list l s =
  match l with
      [] -> s
    | hd::tl -> donotcare_list tl (donotcare_subset hd s)
 
external clause_distribution : clause_set -> clause_set -> clause_set = "clause_distribution"
external clause_distribution_bdd: clause_set -> clause_set -> clause_set = "clause_distribution_bdd"
external get_empty_set : unit -> clause_set = "get_empty_set"
let get_empty_clause () =
  build_clause []
(*
external get_dd : clause_set -> bdd = "get_dd"
external get_bdd : clause_set -> bdd = "get_bdd"
external from_dd : bdd -> clause_set = "from_dd"
external from_bdd : bdd -> clause_set = "from_bdd"
*)

let empty_set = get_empty_set ()
let empty_clause = get_empty_clause ()

let rec support_to_zdd x = 
  if (x = bdd_one) || (x = bdd_zero) then (
    empty_clause
  ) else (
(*    print_int (bdd_top x);
    print_string " ";
    flush_all ();*)
    getzdd (bdd_top x) (support_to_zdd (bdd_t x)) (empty_set)
  )

let vars_support cl = 
  let cl' = get_support cl in
  let rec add_top_var cl s = 
    if cl = bdd_one then 
      s 
    else 
      let s' = IntSet.add ((bdd_top cl)/2) s in 
	add_top_var (bdd_t cl) s'
  in
  let s = add_top_var cl' IntSet.empty in
    s

let vars_support_z cl = 
  let cl' = get_support cl in
  let rec add_top_var cl s = 
    if (cl = bdd_one) || (cl = bdd_zero) then 
      s 
    else 
      let s' = IntSet.add (bdd_top cl) s in 
	add_top_var (bdd_t cl) s'
  in
  let s = add_top_var cl' IntSet.empty in
(*    print_int_list (IntSet.elements s);
    print_string "\n";*)
    s

let filter_support s = 
  let v = vars_support_z s in
  let vl = IntSet.elements v in
  let rec clean vl v = 
    match vl with
	[] -> v
      | hd::tl -> let hd' = if (hd mod 2=1) then (hd-1) else (hd+1) in
	let v' = if (IntSet.mem hd' v) then
	  IntSet.remove hd' (IntSet.remove hd v)
	else v
	in
	  clean tl v'
  in
    clean vl v

let find_pure_literals s = 
(*  let x = filter_tautology (support_to_zdd (get_support s)) in
    print_string "\n";
    x*)
  let fs = filter_support s in
(*    print_int_list (IntSet.elements fs);
    print_string "\n";*)
    let c = build_clause (List.map (fun x -> if (x mod 2=1) then -(x/2) else (x/2)) (IntSet.elements fs)) in
      print_int_list (IntSet.elements (vars_support_z c));
      print_string "\n";
      c

let find_qbf_pure_literals s = 
  qbf_pure_adjust (find_pure_literals s)

let find_appliable_literals s = 
  let l1 = find_unit_literals s in
  let l2 = find_pure_literals s in
(*    clause_distribution l1 l2 *)
  let x = IntSet.elements (IntSet.union (vars_support_z l1) (vars_support_z l2)) in
(*    print_int_list x;
    print_string "\n";*)
    build_clause (List.map (fun x -> if (x mod 2=1) then -(x/2) else (x/2)) x)

let resolve_var i s =
  if debug_dump then (
    print_int (clause_set_size s);
    print_string "->";
    flush_all ()) else ();
  let (st, sf, sn) = split_subset i s in
    if debug_dump then (print_int (clause_set_size st);
			print_string " ";
			print_int (clause_set_size sf);
			print_string " ";
			print_int (clause_set_size sn);
			print_string "->";
			flush_all () ) else ();
  let s' = clause_distribution st sf in
    if debug_dump then (  print_int (clause_set_size s');
			  print_string "^";
			  flush_all () ) else ();
    (*  let s'' = subsumption_free_union s' sn in
	print_int (clause_set_size s'');
	print_string "\n";
	flush_all () ) else ();*)
    s'

let resolve_var_list i sl =
  let _ = List.map (fun x -> print_int (clause_set_size x); print_string " ") sl in
  let x = List.fold_left subsumption_free_union empty_set sl in
(*  let (st, sf, sn) = split_subset i x in*)
  let result = resolve_var i x in
    [result]
	 
(*
let resolve_var_list i sl = 
  let is_empty x = if x = empty_set then false else true in
  let sl' = List.map (split_subset i) sl in
  let (x, sn) = List.split sl' in
  let (st, sf) = List.split x in
  let st' = List.filter is_empty st in
  let sf' = List.filter is_empty sf in
  let sn' = List.filter is_empty sn in
  let t = List.fold_left subsumption_free_union empty_set st' in
  let f = List.fold_left subsumption_free_union empty_set sf' in
  let n = clause_distribution t f in
    n::sn
*)

let var_used i s = 
  let s' = donotcare_subset i s in
    if (s' = s) then false else true
      
let prop_bdr s l b = 
  let x = ref s in
  let j = ref 0 in
    while !j < l do
      let (xt, xf, xn) = split_subset !j !x in
      let xx = 
	if ((clause_set_size xt) < b) && ((clause_set_size xf) < b) then
	  let _ = Printf.printf "resolving %d\n" !j in
	  let _ = flush_all () in
	    subsumption_free_union xn (clause_distribution xt xf)
	else
	  !x
      in
	x := xx;
	j := !j + 1;
    done;
    !x
