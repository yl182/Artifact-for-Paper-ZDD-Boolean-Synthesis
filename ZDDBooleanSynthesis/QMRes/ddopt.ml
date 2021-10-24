open Common
open Cudd
open Qbfformula
open Qbf

let rec max_cardinality_ordering sl v =
  let card l g v = 
    let s = Array.get g v in
    let s' = IntSet.inter s l in
      IntSet.cardinal s'
  in
  let build_interference_graph sl v =
    let vmax = IntSet.max_elt v in
    let g = Array.make (vmax+1) IntSet.empty in
    let add_support s =
      let s' = IntSet.elements s in
      let add_support_int l = 
	let add_support_int_2 x l =
	  let _ = List.map (fun y -> let s = Array.get g x in
			    let s' = IntSet.add y s in
			    let _ = Array.set g x s' in
			    let s = Array.get g y in
			    let s' = IntSet.add x s in
			    let _ = Array.set g y s' in
			      ()
			   ) l in
	    ()
	in
	match l with 
	    [] -> ()
	  | hd::tl -> add_support_int_2 hd tl
      in
	add_support_int s'
    in
    let _ = List.map add_support sl in
      g
  in
  let rec max_card_int lc lc' g v =
    let rec max_card_search v = 
      let hd::tl = v in
      let h' = card lc' g hd in
      let rec max_card_search_int r m mc v =
	match v with
	    [] -> (m,r)
	  | hd::tl -> let h' = card lc' g hd in
	      if (h' > mc) then
		max_card_search_int (m::r) hd h' tl
	      else
		max_card_search_int (hd::r) m mc tl
      in
	max_card_search_int [] hd h' tl 
    in
    match v with
	[] -> lc
      | _ -> let (x,v') = max_card_search v in
	  max_card_int (x::lc) (IntSet.add x lc') g v'
  in
  let g = build_interference_graph sl v in
  let g' = Array.map IntSet.cardinal g in
  let mc = 0 in
  let mcw = -1 in
  let mcref = ref mc in
  let mcwref = ref mcw in
    for i = 0 to ((Array.length g') - 1) do
      if g'.(i) > !mcwref then
	(
	  mcref := i;
	  mcwref := g'.(i);
	)
    done;
    max_card_int [!mcref] (IntSet.add !mcref IntSet.empty) g (IntSet.elements (IntSet.remove !mcref v))

let rec support f = 
  match f with
      `True | `False | `Invalid -> IntSet.empty
    | `Prop(i) -> IntSet.singleton i
    | `Not(g) -> support g
    | `And(l) | `Or(l) -> let l' = List.map support l in
	List.fold_left IntSet.union IntSet.empty l'
    | `Quant(q,g) -> support g
	
let rec map_vars vo f =
  match f with 
      `Prop(i) -> `Prop(vo.(i))
    | `Not(g) -> `Not(map_vars vo g)
    | `And(l) -> `And(List.map (map_vars vo) l)
    | `Or(l) -> `Or(List.map (map_vars vo) l)
    | `Quant(q,g) ->
	let (qu, qv) = q in
	let qv' = List.map (fun y -> vo.(y)) qv in
	  `Quant((qu,qv'), map_vars vo g)
    | _ -> f

let rec print_int_list l =
  match l with
      [] -> ()
    | hd::tl -> print_int hd; print_string " "; print_int_list tl

let shuffle_vars f =
  let vf = props f in
  let (f',q') = prenex_noshare_split f in
  let f'' = cnf f' vf in
    match f'' with
	`And(l) -> 
	  let ls = List.map support l in
	  let vs = List.fold_right IntSet.union ls IntSet.empty in
	  let vo = max_cardinality_ordering ls vs in
	  let vo' = List.filter (fun x -> if (x<=vf) then true else false) vo in
	  let vo'' = Array.of_list vo' in
	  let vo''' = Array.make (vf+1) 0 in
	  let _ = Array.iteri (fun i x -> vo'''.(x) <- i) vo'' in
	  let f''' = map_vars vo''' f in
	    f'''
      | _ -> f

let rec and_exist_opt_bucket vars dds =
  match vars with
      [] -> List.fold_right bdd_and dds bdd_one
    | hd::tl ->
	let dd_vars = List.map bdd_var_set dds in
	let dd_pair = List.combine dds dd_vars in
	let (conj, other) = List.partition (fun (a,b) -> if (IntSet.mem hd b) then true else false) dd_pair in
	let (dds',_) = List.split conj in
	let (otherdds',_) = List.split other in
	let cur = List.fold_right bdd_and dds' bdd_one in
	let cur' = bdd_exists (bdd_var hd) cur in
	  and_exist_opt_bucket tl (cur'::otherdds')

let and_exist_opt_bucket_vo vars dds = 
  let dd_vars = List.map bdd_var_set dds in
  let v' = max_cardinality_ordering dd_vars vars in
    and_exist_opt_bucket v' dds
    
let rec list_schedule_opt l op z =
  let sort_size l =
    let lsize = List.map bdd_size l in
    let lm = List.combine lsize l in
    let lm' = List.sort (fun (a,b) (a',b') -> Pervasives.compare a' a) lm in
    let (_,l') = List.split lm' in
      l'
  in
  let sort_interference l d =
    let dv = bdd_var_set d in
    let lv = List.map bdd_var_set l in
    let ivs = List.map (fun a -> IntSet.cardinal (IntSet.inter a dv)) lv in 
    let ls = List.combine ivs l in
    let ls' = List.sort (fun (a,b) (a',b') -> Pervasives.compare a' a) ls in
    let (_,l') = List.split ls' in
      l'
  in
  match l with
      [] -> z
    | [x] -> x
    | hd::tl -> 
	let l' = sort_size l in
	let hd::tl = l' in
	let l'' = sort_interference tl hd in
	let hd'::tl' = l'' in
(*	let _ = print_int (bdd_size hd) in
	let _ = print_string " " in
	let _ = print_int (bdd_size hd') in
	let _ = print_string "# " in
	let _ = flush stdout in*)
	let work = op hd hd' in
	  list_schedule_opt (work::tl') op z 

let list_op l op z = 
  if (List.length l) > 5 then
    list_schedule_opt l op z
  else
    List.fold_right op l z
