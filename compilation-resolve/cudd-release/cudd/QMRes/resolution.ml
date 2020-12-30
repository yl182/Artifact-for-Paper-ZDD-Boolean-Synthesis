open Common
open Varorder
open Cudd
open Zres
open Clauseset
open Options

type sat_result = Satisfied | Unsatisfied | Unknown
exception Resolution_done

let var_quantifier_is_exist v qm = if (qm.(v) mod 2=1) then true else false

let bdd_sum_list l = match l with 
    [] -> bdd_one
  | _ -> List.fold_left bdd_and bdd_one l

class virtual ['b] abstract_resolution = 
object (_:'a)
  method virtual resolve: 'a list
  method virtual check: sat_result
  method virtual check_termination: bool -> bool
  method virtual size: int
  method virtual priority: int
  method virtual completed: bool
  method virtual top_branch_existential: bool
  method virtual get_data: 'b
  method virtual set_data: 'b -> unit
  method virtual depth:int
end

class incbddres bh s qo' bo' qm = 
object (self:clause_set #abstract_resolution)
  val mutable bm = IntMap.empty
  val mutable s = s
  val mutable qo = qo'
  val mutable qosize = List.length qo'
  val mutable bo = bo'
  val mutable bh = bh
  val mutable us = false
  val mutable sat = false
  val depth = List.length bo'
  val qm = qm
  method depth = depth
  method set_data s' = s <- s'
  method get_data = s
  method completed = qo = []
  method size = clause_set_size s
  method priority = -qosize
  method top_branch_existential = let (qt, _)::_ = bo in qt
  method resolve = 
    match qo with
	[] -> (
(*	  Printf.printf "Resolution done???";
	  raise Resolution_done*)
	  [{<sat=true>}]
	)
      | hd::tl -> 
	  (
	    let s' = Branching.simp_unit_pure s in
	    let (t,f,n) = split_subset hd s' in
	    let t' = bdd_or (bdd_var hd) (bddnoquant t) in
	    let f' = bdd_or (bdd_not (bdd_var hd)) (bddnoquant f) in
	    let x = bdd_and t' f' in
	    let b = if IntMap.mem hd bm then bdd_sum_list (IntMap.find hd bm) else bdd_one in
	      let x' = 
		if not(var_quantifier_is_exist hd qm) then (
		  let x'' = bdd_and b x in
		  let x''' = bdd_forall (bdd_var hd) x'' in
		    x'''
		) else (
		  let x' = bdd_andexist b x (bdd_var hd) in
		    x'
		) in
	      let (n',x'') = if (!zres_use_bdd) then (
		if (bdd_size x') > !bdd_threshold then (
		  if !zres_split_bdd then (
		    let (xx, nn) = bddsplit x' in
		    let nnn = subsumption_free_union n nn in
		      (nnn, xx)
		  ) else (
		    let xc = bdd2clauseset x' in
		    let nn = subsumption_free_union n xc in
		      (nn,bdd_one)
		  )
		) else
		  (n,x')
	      ) else
		(n,x') in
	      let us' = if (x'' = bdd_zero) then true else false in
	      let bm' = IntMap.remove hd bm in
	      let tv = bdd_top x'' in
	      let l' = if (IntMap.mem tv bm') then (IntMap.find tv bm') else [] in
	      let l'' = x''::l' in
	      let bm'' = IntMap.add hd l'' bm' in
	      let _ = Printf.printf "elim = %d, tv = %d\n" hd tv in
		[{< s=n'; bm=bm'';qo=tl;qosize=qosize-1;us=us' >}]
	  )
  method check =
    if (sat = true) then Satisfied
    else if ((s = empty_clause) or (us = true)) then Unsatisfied
    else Unknown
method check_termination is_exist = 
  if !debug_resolution > 1 then 
      Printf.printf "Checking termination exist=%s\n" (if is_exist then "true" else "false");
    let ck = self#check in
      if !debug_resolution > 1 then
	Printf.printf "Check result = %s\n" (if ck=Satisfied then "SAT" else if ck=Unsatisfied then "UNSAT" else "UNKNOWN");
      if (ck=Satisfied && is_exist) or (ck=Unsatisfied && not is_exist) then true
      else false
end

class bddres bh s qo' bo' qm = 
object (self:clause_set #abstract_resolution)
  val mutable b = bdd_one
  val mutable s = s
  val mutable qo = qo'
  val mutable qosize = List.length qo'
  val mutable bo = bo'
  val mutable bh = bh
  val depth = List.length bo'
  val qm = qm
  method depth = depth
  method set_data s' = s <- s'
  method get_data = s
  method completed = qo = []
  method size = clause_set_size s
  method priority = -qosize
  method top_branch_existential = let (qt, _)::_ = bo in qt
  method resolve = 
    match qo with
	[] -> (
	  Printf.printf "Resolution done???";
	  raise Resolution_done
	)
      | hd::tl -> 
    if (!Options.measure_size) then (
      max_nodes := max (!max_nodes) (bdd_size b);
    );
	  if Options.check_bdd_branching (bdd_size b) then (
	    let (bl,bo',alt, v) = bh#branch (b,s) bo hd in
	      List.map (fun (x,y) -> {< s=y;b=x; bo=bo';depth=List.length bo' >} ) bl
	  ) else (
	    let s' = Branching.simp_unit_pure s in
	    let (t,f,n) = split_subset hd s' in
	    let t' = bdd_or (bdd_var hd) (bddnoquant t) in
	    let f' = bdd_or (bdd_not (bdd_var hd)) (bddnoquant f) in
	    let x = bdd_and t' f' in
	      if !debug_resolution > 0 then (
		Printf.printf "BDD size %d,%d " (bdd_size b) (bdd_size x);
		flush_all ();
	      );
	      let x' = 
		if not(var_quantifier_is_exist hd qm) then (
		  let x'' = bdd_and b x in
		  let x''' = bdd_forall (bdd_var hd) x'' in
		    x'''
		) else (
		  let x' = bdd_andexist b x (bdd_var hd) in
		    x'
		) in
	      let (n',x'') = if (!zres_use_bdd) then (
		if (bdd_size x') > !bdd_threshold then (
		  if !zres_split_bdd then (
		    let (xx, nn) = bddsplit x' in
		    let nnn = subsumption_free_union n nn in
		      (nnn, xx)
		  ) else (
		    let xc = bdd2clauseset x' in
		    let nn = subsumption_free_union n xc in
		      (nn,bdd_one)
		  )
		) else
		  (n,x')
	      ) else
		(n,x') in
		[{< s=n'; b=x'';qo=tl;qosize=qosize-1 >}]
	  )
  method check =
    if ((s = empty_set) && (b = bdd_one)) then Satisfied
    else if ((s = empty_clause) or (b = bdd_zero)) then Unsatisfied
    else Unknown
method check_termination is_exist = 
  if !debug_resolution > 1 then 
      Printf.printf "Checking termination exist=%s\n" (if is_exist then "true" else "false");
    let ck = self#check in
      if !debug_resolution > 1 then
	Printf.printf "Check result = %s\n" (if ck=Satisfied then "SAT" else if ck=Unsatisfied then "UNSAT" else "UNKNOWN");
      if (ck=Satisfied && is_exist) or (ck=Unsatisfied && not is_exist) then true
      else false
end
  
class zr bh s qo' bo' qm =  
object (self:clause_set #abstract_resolution)
  val mutable s = s
  val mutable qo = qo'
  val mutable qosize = List.length qo'
  val mutable bo = bo'
  val mutable bh = bh
  val mutable depth = List.length bo'
  val qm = qm
  method depth = depth
  method set_data s' = s <- s'
  method get_data = s
  method completed = qo = []
  method size = clause_set_size s
  method priority = -qosize
  method top_branch_existential = let (qt, _)::_ = bo in qt
  method resolve = 
    if !debug_resolution > 1 then (
      print_string "qo is ";
      print_int_list qo;
      print_string "\n";
      flush_all ();
    );
    if (!Options.measure_size) then (
      max_nodes := max (!max_nodes) (clause_set_size s);
      max_clauses := max (!max_clauses) (clause_set_clauses s);
    );
    match qo with
	[] -> (
	  Printf.printf "Resolution done???";
	  raise Resolution_done
	)
      | hd::tl -> 
	  if !debug_resolution > 0 then (
	    Printf.printf "size of s = %d" (clause_set_size s);
	    flush_all ();
	  );
	  if not(var_quantifier_is_exist hd qm) then (
	    let s' = universal_abstract hd s in
	      if !debug_resolution > 0 then (
		Printf.printf "removing univ size of s' = %d" (clause_set_size s');
		flush_all ();
	      );
	      [{< s=s';qo=tl;qosize=qosize-1 >}]
	  ) else (
	    let (t,f,n) = split_subset hd s in
	      if !debug_resolution > 0 then 
		Printf.printf " splitting on %d " hd;
	      if Options.check_branching (clause_set_size t) (clause_set_size f) then
		let (bl,bo',alt, v) = bh#branch s bo hd in
		  List.map (fun x -> {< s=x; bo=bo';depth=List.length bo' >} ) bl
	      else (
		if !debug_resolution > 0 then (
		  Printf.printf "Resolving %d to %d\n" (clause_set_size t) (clause_set_size f);
		  flush_all ();
		);
		let x = if !zres_use_bdd then 
		  clause_distribution_bdd t f 
		else clause_distribution t f in
		  if !debug_resolution > 0 then (
		    Printf.printf "size = %d\n" (clause_set_size x);
		    flush_all ();
		  );
		  let s' = subsumption_free_union x n in
		  let s'' = Branching.simp_unit_pure s' in
		    if !debug_resolution > 0 then (
		      Printf.printf "size of s' = %d" (clause_set_size s'');
		      flush_all ();
		    );
		    [{< s=s'';qo=tl;qosize=qosize-1 >}]
	      )
	  )
  method check = 
      if s = empty_set then Satisfied
      else if s = empty_clause then Unsatisfied
      else Unknown
  method check_termination is_exist = 
    if !debug_resolution > 0 then 
      Printf.printf "Checking termination exist=%s\n" (if is_exist then "true" else "false");
    let ck = self#check in
      if !debug_resolution > 0 then
	Printf.printf "Check result = %s\n" (if ck=Satisfied then "SAT" else if ck=Unsatisfied then "UNSAT" else "UNKNOWN");
      if (ck=Satisfied && is_exist) or (ck=Unsatisfied && not is_exist) then true
      else false
end

class unlayeredzr bh s qo bo qm us = 
object (self)
  inherit zr bh s qo bo qm as super
  val us = us
  method resolve = let res = super#resolve in
    List.map (fun x -> x#set_data (us x#get_data);x) res
end

class taggedzr obj = 
object (self:clause_set #abstract_resolution)
  val mutable tag = 0
  val obj = obj
  method get_tag = tag
  method set_tag t = tag <- t
  method set_data = obj#set_data
  method get_data = obj#get_data
  method depth = obj#depth
  method check = obj#check
  method completed = obj#completed
  method check_termination = obj#check_termination
  method size = obj#size
  method priority = obj#depth * 10000 + obj#size
  method top_branch_existential = obj#top_branch_existential
  method resolve = let make x = {< tag=0;obj=x >} in
    List.map make obj#resolve
end

module MultiResolution = struct
  type t = taggedzr
  let compare a b = Pervasives.compare a#priority b#priority
end

