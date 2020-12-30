open Common
open Qbfformula

let is_true f = if (f = `True) then true else false
let is_false f = if (f = `False) then true else false
let not_true f = if (f = `True) then false else true
let not_false f = if (f = `False) then false else true

let rec print f = 
  match f with
      `True -> print_string "true"
    | `False -> print_string "false"
    | `Prop(i) -> print_string "p"; print_int i
    | `Not(g) -> print_string "~("; print g; print_string ")"
    | `And(l) -> print_and l
    | `Or(l) -> print_or l
    | `Quant(q, g) -> print_quantifier q; print_string "("; print g; print_string ")"
    | _ -> print_string " Invalid "
and print_and l =
  match l with
      [f1;f2] -> print_string "("; print f1; print_string " & "; print f2; print_string ")"
    | hd :: tl -> print_string "("; print hd; print_string " & "; print_and tl; print_string ")"
    | _ -> ()
and print_or l =
  match l with
      [f1;f2] -> print_string "("; print f1; print_string " v "; print f2; print_string ")"
    | hd :: tl -> print_string "("; print hd; print_string " v "; print_or tl; print_string ")"
    | _ -> ()
and print_quantifier q =
  let (qtype, qlist) = q in
    match qlist with
	[] -> ()
      | hd::tl -> ( match qtype with 
	    `Forall -> print_string " forall "
	  | `Exists -> print_string " exists "
		  );
	  let x = `Prop(hd) in
	    print x;
	  print_quantifier (qtype, tl)

let parse_dimacs name = 
  let inf = open_in name in
  let lexbuf = Lexing.from_channel inf in
    try 
      let result = Dimacsparser.main Dimacslex.token lexbuf in
	result
    with _ -> print_string (Lexing.lexeme lexbuf); `Invalid
      
let print_cnf_prop f =
  let rec print_clauses l = 
    match l with
	[] -> ()
      | hd::tl -> print_cnf_clause hd;
	  print_clauses tl
  and print_cnf_clause cl = 
    match cl with
	`Or(l) -> 
	  print_lits l;
	  print_string " 0 \n"
      | _ -> ()
  and print_lits l =
    match l with
	hd::tl -> ( match hd with
			`Prop(i) -> print_int i; print_string " "
		      | `Not(`Prop(i)) -> print_int (-i); print_string " "
		      | _ -> ()
		  );
	  print_lits tl
      | _ -> ()
  in
    match f with
	`And(l) -> 
	  print_clauses l
      | _ -> ()

let rec simplify f =
  match f with
      `True | `False | `Prop(_) | `Invalid -> f
    | `Not(`True) -> `False
    | `Not(`False) -> `True
    | `Not(g) -> `Not(simplify g)
    | `Quant(q, g) -> `Quant(q, simplify g)
    | `And(l) -> let l' = List.map simplify l in
      let l' = flatten_and l' in
      if (List.exists is_false l') then
	`False
      else (
	let l'' = List.filter not_true l' in 
	  match l'' with
	      [] -> `True
	    | hd::tl -> match tl with
		  [] -> hd
		| _ -> `And(l'')
      )
    | `Or(l) -> let l' = List.map simplify l in
      let l' = flatten_or l' in
      if (List.exists is_true l') then
	`True
      else (
	let l'' = List.filter not_false l' in
	  match l'' with
	      [] -> `False
	    | hd::tl -> match tl with
		  [] -> hd
		| _ -> `Or(l'')
      )
and flatten_and l =
  let is_and f = (
    match f with
	`And( l ) -> true
      | _ -> false
  ) in
  let strip_and f = (
    match f with
	`And( l ) -> l
      | _ -> []
  ) in
    flatten_op is_and l strip_and
and flatten_or l =
  let is_or f = (
    match f with
	`Or( l ) -> true
      | _ -> false
  ) in
  let strip_or f = (
    match f with
	`Or( l ) -> l
      | _ -> []
  ) in
    flatten_op is_or l strip_or
and flatten_op pred l strip =
  let (l1, l2) = List.partition pred l in
    match l1 with
	[] -> l2
      | _ -> List.rev_append l2 (flatten_op pred (List.concat (List.map strip l1)) strip)

let rec nnf f =
  match f with
      `True | `False | `Invalid | `Prop(_) -> f
    | `Or(l) -> `Or(List.map nnf l)
    | `And(l) -> `And(List.map nnf l)
    | `Quant(q,g) -> `Quant(q, nnf g)
    | `Not(g) -> neg g
    | _ -> `Invalid
and neg f =
  match f with
      `True -> `False
    | `False -> `True
    | `Prop(i) -> `Not(`Prop(i))
    | `Not(g) -> nnf g
    | `And(l) -> `Or(List.map neg l)
    | `Or(l) -> `And(List.map neg l)
    | `Quant((`Exists,q),g) -> `Quant((`Forall,q),neg g)
    | `Quant((`Forall,q),g) -> `Quant((`Exists,q),neg g)
    | _ -> `Invalid

let prenex_noshare_split f =
  let rec prenex_int (f,q) =  
    match f with
	`True | `False | `Invalid | `Prop(_) -> (f,q)
      | `Not(g) -> let (g', q') = prenex_int (g, q) in
	  (`Not(g'), q')
      | `Quant(q', g) -> let (g', q'') = prenex_int (g, (q @ [q'])) in
	  (g', q'')
      | `And(l) -> let (q', l') = List.fold_right prenex_list l (q, []) in
	  (`And(l'), q')
      | `Or(l) -> let (q', l') = List.fold_right prenex_list l (q, []) in
	  (`Or(l'), q')
  and prenex_list f (q,l) =
    let (f',q') = prenex_int (f,q) in
    let l' = f'::l in
      (q', l')
  in
  let (f',q') = prenex_int (f, []) in
    (f',q')

let prenex_noshare f =
  let (f',q') = prenex_noshare_split f in
    unroll_quant f' q'

let rec strip_quant f = 
  match f with
      `Quant(q, g) -> let (g',q') = strip_quant g in
	(g',q::q')
    | _ -> (f, [])

let quantify_all f = 
  let p = props f in
  let rec all_props p = 
    if (p>0) then
      IntSet.add p ( all_props (p-1) )
    else 
      IntSet.empty
  in
  let allvar = all_props p in
  let rec remove_quantified_vars v f =
    match f with
	`Quant((_, l), g) -> let remove_vars = List.fold_right IntSet.add l IntSet.empty in
	let v' = IntSet.diff v remove_vars in
	  remove_quantified_vars v' g
      | _ -> v
  in
  let v = remove_quantified_vars allvar f in
  let (f',q) = strip_quant f in
    unroll_quant (`Quant((`Exists, (IntSet.elements v)), f')) q

let print_cnf_qbf f = 
  let p = props f in
  let (f',q) = strip_quant f in
  let size = match f' with
      `And(l) -> List.length l
    | _ -> 0
  in
  let rec print_quantifiers q qt =
    let rec print_vars l = 
      match l with
	  hd::tl -> print_int hd; print_string " "; print_vars tl
	| _ -> ()
    in
      match q with
	  hd::tl -> print_string "q ";
	    ( match hd with
		  (q', l) when q'=qt -> print_vars l;
		    print_string "0\n";
		    if (qt = `Exists) then
		      print_quantifiers tl `Forall
		    else
		      print_quantifiers tl `Exists
		| _ -> print_string "0\n";
		    if (qt = `Exists) then
		      print_quantifiers q `Forall
		    else
		      print_quantifiers q `Exists
	    )
	| _ -> ()
  in
    print_string "p cnf ";
    print_int p;
    print_string " ";
    print_int size;
    print_string "\n";
    print_quantifiers q `Exists;
    print_cnf_prop f'
      
let cnf f v =
(*  let pf = props f in*)
  let rec cnf_int f i =
    match f with
	`Invalid | `Quant(_,_) -> (0,i,[])
      | `True -> (*cnf_int (`Or([`Prop(1);`Not(`Prop(1))])) i*)
	  (i, i+1, [`Or([`Prop(i)])])
      | `False -> (*cnf_int (`And([`Prop(1);`Not(`Prop(1))])) i*)
	  (i, i+1, [`Or([`Not(`Prop(i))])])
      | `Prop(j) -> (j,i,[])
      | `Not(g) -> let (i',maxi,cl) = cnf_int g i in
	 (* print_string "new var ";print_int maxi;print_string " ";print f;print_string "\n";*)
	let newcl = `Or([`Not(`Prop(maxi));`Not(`Prop(i'))]) in
	let newcl' = `Or([`Prop(maxi);`Prop(i')]) in
	  ((maxi), (maxi+1), newcl::(newcl'::cl))
      | `And(l) -> let (il, maxi, cl) = cnf_list_int l i in
	  (*print_string "new var ";print_int maxi;print_string " ";print f;print_string "\n";*)
	let clause_1 = `Or(`Prop(maxi)::(List.map (fun i -> `Not(`Prop(i))) il)) in
	let clauses = List.map (fun i' -> `Or([`Prop(i');`Not(`Prop(maxi))])) il in
	  (maxi, (maxi+1), clause_1::(clauses@cl))
      | `Or(l) -> let (il, maxi, cl) = cnf_list_int l i in
	 (* print_string "new var ";print_int maxi;print_string " ";print f;print_string "\n";*)
	let clause_1 = `Or(`Not(`Prop(maxi))::(List.map (fun i -> `Prop(i)) il)) in
	let clauses = List.map (fun i' -> `Or([`Not(`Prop(i'));`Prop(maxi)])) il in
	  (maxi, (maxi+1), clause_1::(clauses@cl))
      | _ -> (0,i,[`Invalid])
  and cnf_list_int l i =
    match l with 
	[] -> ([], i, [])
      | hd::tl -> let (i',maxi, cl) = cnf_int hd i in
	let (il, maxi', cll) = cnf_list_int tl maxi in
	  (i'::il, (max maxi maxi'), cl@cll)
  in
  let (i, maxi, cl) = cnf_int f (v+1) in
    `And(`Or([`Prop(i)])::cl)

let cnf_q f v =
  let push_quants ql q =
    match ql with
	[] -> [q]
      | hd::tl -> let (ht, hl) = hd in
	let (qt, qq) = q in
	  if (ht = qt) then 
	    (ht,qq @ hl)::tl
	  else
	    q::ql
  in
  let add_quants q vl = 
    let vl' = List.filter (fun i -> if (i > v) then true else false) vl in
    push_quants q (`Exists,vl') in
  let get_prop i = if i>0 then `Prop(i) else `Not(`Prop(-i)) in
  let get_neg_prop i = if i>0 then `Not(`Prop(i)) else `Prop(-i) in
  let rec cnf_int f q i =
    match f with
	`True ->
	  (i, i+1, q, [`Or([`Prop(i)])])
      | `False -> 
	  (i, i+1, q, [`Or([`Not(`Prop(i))])])
      | `Prop(j) -> (j,i,q, [])
      | `Not(`Prop(j)) -> (-j,i,q, [])
      | `Quant(qq,g) -> let (i',maxi, q',cl) = cnf_int g q i in
	let q'' = push_quants q' qq in
	  (i',maxi, q'', cl)
      | `And(l) -> let (il, maxi, q', cl) = cnf_list_int l q i in
	let clause_1 = `Or(`Prop(maxi)::(List.map get_neg_prop il)) in
	let clauses = List.map (fun i' -> `Or([(get_prop i');`Not(`Prop(maxi))])) il in
	let q'' = add_quants q' il in
	  (maxi, (maxi+1), q'', clause_1::(clauses@cl))
      | `Or(l) -> let (il, maxi, q', cl) = cnf_list_int l q i in
	let clause_1 = `Or(`Not(`Prop(maxi))::(List.map get_prop il)) in
	let clauses = List.map (fun i' -> `Or([(get_neg_prop i');`Prop(maxi)])) il in
	let q'' = add_quants q' il in
	  (maxi, (maxi+1), q'', clause_1::(clauses@cl))
      | _ -> (0,i, [], [`Invalid])
  and cnf_list_int l q i =
    match l with 
	[] -> ([], i, q, [])
      | hd::tl -> let (i',maxi, q', cl) = cnf_int hd q i in
	let (il, maxi', q'', cll) = cnf_list_int tl q' maxi in
	  (i'::il, (max maxi maxi'), q'', cl@cll)
  in
  let (i, maxi, q, cl) = cnf_int f [] (v+1) in
  let q' = add_quants q [i] in
  let f' = `And(`Or([get_prop i])::cl) in
(*    print_cnf_qbf f';*)
    unroll_quant f' q'

(*let cnf_qbf f = 
  let v = props f in
  let (f',q') = prenex_noshare_split f in
  let f'' = cnf f' v in
    unroll_quant f'' q'
*)
let cnf_qbf f =
  let f' = nnf f in
  let v = props f' in
  let f'' = cnf_q f' v in
    f''

