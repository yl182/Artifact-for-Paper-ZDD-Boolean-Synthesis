open Common
open Options
open Zres
open Heap
open Resolution
open Varorder
open Clauseset
open Branching

module RPQ = Heap(MultiResolution)

exception Early_termination of MultiResolution.t

class qbf_prioritized_resolution =  
object (self)
  val h = new RPQ.heap
  val t = Tree.empty ()
  method init s = h#add s
  method resolve = 
    let result = ref Unknown in
    while not h#is_empty do
      let x' = h#max_elt in
      let _ = h#pop in
      let res = x'#resolve in
      let res_count = List.length res in
	if (!Options.debug_resolution > 0) then (
	  Printf.printf " %d branches\n" res_count
	);
      let tag' = if res_count = 1 then x'#get_tag else Tree.add x'#get_tag t in
	try 
	  let _ = List.map 
		    (fun y -> 
		       if y#check_termination x'#top_branch_existential 
		       then raise (Early_termination y)
		       else if y#check <> Unknown then 
			 result := y#check
		       else
			 h#add (let _ = y#set_tag tag' in y)
		    ) res in
	    ()
	with x -> 
	  match x with
	      Early_termination(y) -> 
		result := y#check;
		if res_count = 1 then ( (* *) 
		  if Tree.is_root x'#get_tag t then (
		    h#clear
		  ) else
		    let l = List.filter (fun x -> x#get_tag=x'#get_tag) h#elements in
		    let _ = h#clear in
		    let _ = List.map (fun x -> h#add x) l in
		      ()
		) else ( (* one partition of splitting makes it trivial *)
		    let l = List.filter (fun x -> x#get_tag=tag') h#elements in
		    let _ = h#clear in
		    let _ = List.map (fun x -> h#add x) l in
		      ()		  
		)
	    | _ -> raise x
    done;
      !result
end

let qdd f =
  let (bo,ro,qm,f') = sort_vars f in
  let _ = setbddvars (List.fold_left max 0 ro) in
(*  let _ = if (!Options.no_var_shuffle) then () else ( *)
    let _ = if (!Options.dd_order = Unified) or (!Options.dd_order = Hybrid) then varorder_handle_shuffle f' ro else () (*shuffleheap (List.map (fun x -> x-1) ro) *) in
  let build_order o = 
    let max_elt = List.fold_left Pervasives.max 0 o in
    let array = Array.make (max_elt+2) 0 in
    let rec build_order_int o i = 
      match o with
	  [] -> ()
	| hd::tl -> (
	    array.(hd) <- i;
	    build_order_int tl (i+1)
	  )
    in
    let _ = build_order_int o 1 in
      array
  in
  let _ = if (!Options.dd_order = Elimination) then Varorder.var_dd_order := (List.map (fun x -> x) ro) in
  let sc = if (!Options.dd_order = Unified) then (fun x -> sort_clauses_reordered x (build_order !(Varorder.var_dd_order))) else sort_clauses in
  let s = if (!Options.dd_order = Unified) then 
    make_clause_set_fast_recursive f'
  else
    make_clause_set_fast f' sc 
  in
(*  let _ = if (!Options.dd_order = Unified) then varorder_handle_shuffle f' else () in*)
(*  let _ = if (!Options.dd_order = Unified) or (!Options.dd_order = Hybrid) then varorder_handle_shuffle f' ro else shuffleheap (List.map (fun x -> x-1) ro) in*)
  let branching = new zr_branching in
  let elem = match !res_alg with
      Resolution -> (
	match !qo_alg with
	    Layered -> new zr branching s ro bo qm
	  | Arbitary -> new unlayeredzr branching (remove_universal_arbitary s) ro bo qm remove_universal_arbitary
	  | ExistBeforeUniv -> new unlayeredzr branching (remove_universal_exist_before_univ s) ro bo qm remove_universal_exist_before_univ
      ) 
    | BDD -> new bddres (new bdd_branching) s ro bo qm
  in
  let elem' = new taggedzr elem in
  let prioritized_res = new qbf_prioritized_resolution in
  let _ = prioritized_res#init elem' in
  let _ = if !quiet_output then () else report_time "Begin " in
  let result = prioritized_res#resolve in
    result
