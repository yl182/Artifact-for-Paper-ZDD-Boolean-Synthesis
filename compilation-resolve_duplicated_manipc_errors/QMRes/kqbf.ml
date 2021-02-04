open Kformula
open Mlk


module Formula =
  struct
    type t = formula
    let compare = Pervasives.compare
  end
module FormulaSet = Set.Make(Formula)

module Formulakey = 
  struct 
    type t = formula * int * bool
    let compare = Pervasives.compare
  end
module FormulaVarMap = Map.Make(Formulakey)

module SelectFormulakey =
  struct
    type t = formula * int
    let compare = Pervasives.compare
  end
module SelectFormulaMap = Map.Make(SelectFormulakey)

let use_one_hot_encoding = false

let modal_subformula f = 
  let rec ms_int fl s =
    match fl with
	[] -> s
      | hd::tl ->
	  let s' = FormulaSet.add hd s in
	  let tl' = 
	    match hd with
		True | False | Prop(_) -> tl
	      | And(l) | Or(l) -> (tl @ l)
	      | Not(g) -> g::tl
	      | Modal(m, g) -> tl
	      | _ -> tl
	  in
	    ms_int tl' s' 
  in
    ms_int [f] FormulaSet.empty

let level_particle f = 
  let rec level_particle_int formula_list particle_set_list new_set = 
    match formula_list with
	[] -> 
	  let (m, p) = FormulaSet.partition is_modal new_set in
	    if (FormulaSet.is_empty m) then
	      particle_set_list @ [new_set]
	    else
	      let fl' = FormulaSet.elements m in
	      let fl'' = List.map strip fl' in
	      let psl' = (particle_set_list @ [new_set]) in
		level_particle_int fl'' psl' FormulaSet.empty
      | hd::tl -> level_particle_int tl particle_set_list (FormulaSet.union new_set (modal_subformula hd))
  in
    level_particle_int [f] [] FormulaSet.empty

let build_var_map fsl = 
  let build_var_map_int (m,i,l) s =
    let (s', _) = FormulaSet.partition is_lean s in
    let rec add_form_var_map_int l f (m,i) = 
    match f with
	Modal(ModalOp(Diamond,_), _) -> (
	  if (use_one_hot_encoding) then (
	    let m' = FormulaVarMap.add (f,l,false) (i+1) (FormulaVarMap.add (f,l,true) (i+2) m) in
	      (*	    print_string "added "; print_lwb f; print_int (i+1); print_string "\n";*)
	      (m',i+2)
	  ) else (
	    let m' = FormulaVarMap.add (f,l,false) (i+1) m in
	      (m',i+1)
	  )
	) 
      | _ when (is_lean f)-> (
	  let m' = (FormulaVarMap.add (f, l, false) (i+1) m) in
(*	    print_string "added "; print_lwb f; print_int (i+1); print_string "\n";*)
	    (m', i+1)
	)
      | _ -> (m,i)
    in
    let (m',i') = FormulaSet.fold (add_form_var_map_int l) s (m,i) in
      (m', i', l+1)
  in
  let m = FormulaVarMap.empty in
  let (m',i',_) = List.fold_left build_var_map_int (m,0,0) fsl in
    (m',i')

let rec log_encoding_select_formula offset bits base = 
  if (bits = 0) then `True else (
    let x = offset/2 in
    let y = offset - (2*x) in
    let f = match y with
	0 -> `Prop(base)
      | 1 -> `Not(`Prop(base)) in
    let f' = match bits with
	1 -> f
      | _ -> let g = log_encoding_select_formula x (bits-1) (base+1) in
	  `And([f;g]) in
    let f'' = Qbf.simplify f' in
      f''
  )

let build_choice_map fsl base = 
  let rec log_encoding_vars i = 
    match i with 
	0 -> 0
      | _ -> (log_encoding_vars (i/2)) + 1 in
  let build_choice_map_int (m,level,base) s = 
    let (s',_) = FormulaSet.partition is_diamond s in
    let new_vars = log_encoding_vars (FormulaSet.cardinal s') in
    let new_base = base + new_vars in
    let add_select_formula form (m,i) =
      let f = log_encoding_select_formula i new_vars base in
      let i' = i+1 in
      let m' = SelectFormulaMap.add (form,level) f m in
	(m',i')
    in
    let (m',_) = FormulaSet.fold add_select_formula s' (m,0) in 
      (m',level+1,new_base)
  in
  let m = SelectFormulaMap.empty in
  let (m',_,_) = List.fold_left build_choice_map_int (m,0,base) fsl in
    m'

let witness f m l =
  let rec witness_int m l f =
    try 
      let v = FormulaVarMap.find (f, l, false) m in
	`Prop(v)
    with Not_found ->
    	match f with
	    And(x) -> `And(List.map (witness_int m l) x)
	  | Or(x) -> `Or(List.map (witness_int m l) x)
	  | Not(f) -> `Not(witness_int m l f)
	  | True -> `True
	  | False -> `False
	  | _ -> `Invalid
  in
    match f with
	Modal(_, g) -> witness_int m (l+1) g
      | _ -> `True

let witness_choice s m m' l =
  let (d, _) = FormulaSet.partition is_diamond s in
  let witness_choice_one_hot_int f =
    try 
      let v = FormulaVarMap.find (f, l, true) m in
      let q = witness f m l in
	`Or([`Not(`Prop(v)); q])
    with Not_found ->
      `Invalid
  in
  let witness_choice_binary_int f =
    try 
      let fsel = SelectFormulaMap.find (f, l) m' in
      let q = witness f m l in
	`Or([`Not(fsel); q])
    with Not_found ->
      `Invalid
  in
  let rec witness_choice_int d = 
    match d with
	[] -> `True
      | _ -> if use_one_hot_encoding then 
	  `And(List.map witness_choice_one_hot_int d)
	else
	  `And(List.map witness_choice_binary_int d)
  in
    witness_choice_int (FormulaSet.elements d)

(* Now copy only implies *)

(*
let var_copy s m l =
  let (d, _) = FormulaSet.partition is_diamond s in
  let var_copy_single f =
    let v = FormulaVarMap.find (f, l, false) m in
    let v' = FormulaVarMap.find (f, l, true) m in
      `Or([`Prop(v');`Not(`Prop(v))])
  in
    `And(List.map var_copy_single (FormulaSet.elements d))
*)

let quantify_copy s m m' l q =
  let quant_vars_one_hot s = 
    let find_var_int f = FormulaVarMap.find (f, l, true) m in
    let (d, _) = FormulaSet.partition is_diamond s in
      List.map find_var_int (FormulaSet.elements d)
  in
  let quant_vars_binary s =
    let (d, _) = FormulaSet.partition is_diamond s in
    let s' = FormulaSet.elements d in
      match s' with
	  [] -> []
	| hd::_ -> let f = SelectFormulaMap.find (hd,l) m' in
	    match f with
		`And(l) ->
		  let l' = List.map (fun f -> match f with
					 `Prop(v) -> v
				       | `Not(`Prop(v)) -> v
				       | _ -> -1
				    ) l 		
		  in
		    l'
	      | `Prop(v) -> [v]
	      | `Not(`Prop(v)) -> [v]
	      | _ -> []
  in
  let vars = if use_one_hot_encoding then 
    quant_vars_one_hot s 
  else
    quant_vars_binary s
  in
    if (List.length vars = 0) then
      q
    else
      `Quant((`Forall, vars), q)
      
let tr_quant s s' m l q =
(*  let (s',_) = FormulaSet.partition is_modal s in
  let x = FormulaSet.elements s' in
  let x' = List.map strip x in*)
  let (lean,_) = FormulaSet.partition is_lean s' in 
  let x = FormulaSet.elements lean in
  let find_var_int f = FormulaVarMap.find (f, (l+1), false) m in
  let qv = List.map find_var_int x in
    if (List.length qv = 0) then
      q
    else
      `Quant((`Exists, qv), q)

let tr_level s m l =
  let (b,_) = FormulaSet.partition is_box s in
  let (d,_) = FormulaSet.partition is_diamond s in
  let d' = FormulaSet.elements d in
  let vars = List.map (fun f -> let v = FormulaVarMap.find (f,l,false) m in `Prop(v)) d' in
  let b' = FormulaSet.elements b in
  let box_support_int f =
    let wf = witness f m l in
    let v = FormulaVarMap.find (f, l, false) m in
  (*  let q = witness f m l in *)
    let pv = `Prop(v) in
    let ov = `Or(vars) in
    let pv' = `And([pv;ov]) in
      `Or([`Not(pv'); wf])
  in
  let al = List.map box_support_int b' in
    if (List.length al = 0) then
      `True
    else
      `And(al)

let cons_level s m l =
  let (n,_) = FormulaSet.partition is_not s in
  let n' = FormulaSet.elements n in
  let cons_level_int f = 
    let v = FormulaVarMap.find (f, l, false) m in
    match f with
	Not(g) -> let v' = FormulaVarMap.find (g, l, false) m in
	  `Not(`And([`Prop(v);`Prop(v')]))
      | _ -> `Invalid
  in
    `And(List.map cons_level_int n')

let var_choice_one_hot s m l =
  let not_two_true vars =
    let rec ntt_int1 vl vr l =
      match vl with
	  [] -> l
	| hd::tl -> let l' = ntt_int2 hd vr l in
	    ntt_int1 tl vr l'
    and ntt_int2 f vr l =
      match vr with
	  [] -> l
	| hd::tl -> if (hd = f) then
	    l
	  else
	    let f' = `Not(`And([f;hd])) in
	    let l' = f'::l in
	      ntt_int2 f tl l'
    in
     `And(ntt_int1 vars vars [])
  in
  let (d, _) = FormulaSet.partition is_diamond s in
  let d' = FormulaSet.elements d in
  let vars = List.map (fun f -> let v = FormulaVarMap.find (f,l,true) m in
		       let v' = FormulaVarMap.find (f,l,false) m in
			 (*`Prop(v)*)
			 `And([`Prop(v);`Prop(v')])
		      )
	       d' in
  let vars' = List.map (fun f -> let v = FormulaVarMap.find (f,l,true) m in
			 `Prop(v)
		      )
	       d' in
    match vars with
	[] -> `True
      | _ -> 
	  let not_two = not_two_true vars' in
	    `And([`Or(vars);not_two])

let var_choice_binary s m m' l =
  let (d, _) = FormulaSet.partition is_diamond s in
  let d' = FormulaSet.elements d in
  let choice = List.map (fun f -> let f' = SelectFormulaMap.find (f,l) m' in
			 let v = FormulaVarMap.find (f,l,false) m in
			   `And([f';`Prop(v)])
			)
		 d' in
    match choice with
	[] -> `True
      | _ -> `Or(choice)

let make_qbf_level s s' m m' l q =
  let tr = tr_level s m l in
  let wc = witness_choice s m m' l in
  let img = tr_quant s s' m l (`And([tr;wc;q])) in
  let choice = if use_one_hot_encoding then 
    var_choice_one_hot s m l 
  else
    var_choice_binary s m m' l
  in
(*  let vc = var_copy s m l in*)
  let cons = cons_level s m l in
  let q' = 
    match choice with 
	`True -> 
	  quantify_copy s m m' l (`And([(*vc;cons;*)img]))
      | _ ->
	  quantify_copy s m m' l (`Or([`Not(choice);`And([(*vc;cons;*)img])])) in
(*    `And([vc;q'])*)
    `And([cons;q'])

let make_qbf f fsl =
  let (m,vars) = build_var_map fsl in
  let m' = if use_one_hot_encoding then 
    SelectFormulaMap.empty
  else 
    build_choice_map fsl (vars+1)
  in
  let rec make_qbf_int sl l q =
    match sl with
	[] -> q
      | hd::tl -> 
	  let q' = make_qbf_int tl (l+1) q in
	    match tl with
		[] -> make_qbf_level hd FormulaSet.empty m m' l q'
	      | h'::t' -> make_qbf_level hd h' m m' l q'
  in
  let q = `True in
  let q' = make_qbf_int fsl 0 q in
  let p = FormulaVarMap.find (f,0,false) m in
  let form = `Prop(FormulaVarMap.find (f,0,false) m) in
    `Quant((`Exists,[p]),`And([q';form]))

let get_qbf f =
  let f' = Modal(ModalOp(Diamond, 1), nnf f) in
(*  let f' = opt_prop f in*)
  let fsl = level_particle f' in
  let g = make_qbf f' fsl in
  let g' = Qbf.simplify g in
    g'

let get_qbf_cnf f =
  let g = get_qbf f in
  let g' = Qbf.cnf_qbf g in
(*  let g'' = Qbf.quantify_all g' in*)
    g'
