open Common
open Qbfformula
open Qbf
open Cudd
open Ddopt
open Zres
open Options
open Varorder
open Branching
open Clauseset
(*open Bed*)

let debug_dump = ref false
let debug_learning = ref false
let use_learning = ref false
let always_split = ref false

let print_active = ref false

type sat_alg = Resolution | CNF2DNF | BDD | BDDBUCKET | BDDNOQUANT | BDDALLQUANT | BDDNEXT | BED| REMOVEUNWIT |COMPUTEWIDTH | BDDSCHED | ZDDQUANT

let alg = ref Resolution

let learn_threshold = ref 1.5

let learning_check = ref 0
let learning_check_success = ref 0

let backtracks = ref 0

let rec split_min comp l =
  match l with
      [x] -> (x,[])
(*    | [x;y] -> if (comp x y)<0 then (x,[y]) else (y,[x])*)
    | hd::tl -> let (m,l') = split_min comp tl in
	if (comp hd m)<0 then (hd,m::l') else (m,hd::l')

let rec print_int_list l =
  match l with
      [] -> ()
    | hd::tl -> print_int hd; print_string " "; print_int_list tl

let sort_quant_occurance_new f =
  let sorted f = 
    let vo = match !sort_alg with
	Diversity -> sort_diversity f
      | Degree -> sort_degree f
      | Cardinality -> sort_cardinality f
      | LayeredCardinality -> sort_layered_cardinality f
      | BFS -> sort_rgl_lex f
      | BFSMIN -> sort_rgl_lex_min f
      | MCS -> sort_rgl_mcs f
      | MIW -> sort_rgl_formula f
      | MF -> sort_rgl_formula f
      | NEW -> sort_rgl_formula f
      | None -> List.map (fun x -> x-1) (IntSet.elements (support_vars f))
    in
    let vo' = if !invert_order then List.rev vo else vo in
(*    let width = get_width f vo' in
      Printf.printf "width = %d\n" width;
      dump_time_raw "width.dat" 0 width;
      flush_all ();*)
      vo'
  in
  let var_sorted = sorted f in
    if !debug_varorder > 0 then (
      print_string "vars";
      print_int_list var_sorted;
      print_string "\n";
    );
  let vf = props f in
  let vm = Array.make (vf+1) 0 in
  let _ = List.fold_left (fun i x -> vm.(x+1) <- i; i+1) 1 var_sorted in
    if !debug_varorder > 1 then 
      print_quantifier_map vm;
  let f' = map_vars vm f in
    if !debug_varorder > 1 then
      print f';
  let (f'',q) = prenex_noshare_split f' in
  let vf = props f'' in
    if !debug_varorder > 0 then
      Printf.printf "vf of simplied formula is %d\n" vf;
  let qm = make_quantifier_map q vf in
  let _ = set_quantifier_map qm in
    f'

exception Bad_formula

let sort_quantifiers q = 
  List.map (fun q -> match q with
		(`Exists,l) -> (`Exists, (List.sort Pervasives.compare l))
	      | (`Forall,l) -> (`Forall, (List.sort Pervasives.compare l))
	   ) q
    
let make_clause_zres c = 
  match c with
      `Prop(v) -> build_clause [v]
    | `Not(`Prop(v)) -> build_clause [(-v)]
    | `Or(l) -> let l' = List.map (fun f -> match f with 
				       `Prop(v) -> v
				     | `Not(`Prop(v)) -> (-v)
				     | _ -> raise Bad_formula
				  ) l in
	build_clause l'
    | _ -> raise Bad_formula

exception ZR_UNSAT
exception ZR_SAT
exception ZR_BRANCH of clause_set * clause_set
exception ZR_BRANCH_LEARNING of clause_set * clause_set * int

let rec simp_unit s b = 
  let u = find_unit_literals s in
  let u' = bound_cube u b in
    if u' = empty_clause then
      s
    else (
(*      print_string "*";
      flush_all ();*)
      simp_unit (apply_literals s u') b
    )

let rec simp_pure s b = 
  let u = find_pure_literals s in
  let u' = bound_cube u b in
    if u' = empty_clause then
      s
    else (
(*      print_string "*";
      flush_all ();*)
      simp_pure (apply_literals s u') b
    )

let rec simp_pure_unit s b = 
  let u = find_appliable_literals s in
  let u' = bound_cube u b in
    if u' = empty_clause then
      s
    else (
      if !debug_dump then (print_string "*";      
			   flush_all ()
			  ) else ();
      simp_pure_unit (apply_literals s u') b
    )
(*
let make_clause_set f = 
  let `And(l') = f in
  let l = List.map (fun f -> match f with
			`Or(l) -> l
		      | `Prop(_) | `Not(_) -> [f]
*)
let rec bucket_elim_zres q cl vmax =
  let rec buc_elim_exists mi ma cl bran =
    if !debug_dump then ( print_string "Resolving var ";
			 print_int mi;
			 print_string "\n";
			 flush_all () ) else ();
    try
      let cl' = resolve_var_prop mi cl bran in
	if (cl' = empty_set) or (cl' = empty_clause) then 
	  cl'
	else ( 
	  if mi < ma then 
	    buc_elim_exists (mi+1) ma cl' bran
	  else
	    cl'
	)
    with 
	ZR_BRANCH_LEARNING(fs, ss, dec) ->
	  let cl'' = buc_elim_exists (mi+1) ma fs (dec::bran) in
	    if (!debug_dump) then (
	      print_int (clause_set_size cl'');
	      print_string " ";
	      print_int (mi);
	      print_string "\n";
	      flush_all ();
	    ) else ();
	    if (cl'' = empty_set) then (
	      empty_set
	    ) else (
	      backtracks := !backtracks+1;
	      let ss' = subsumption_free_union ss cl'' in
		buc_elim_exists mi ma ss' bran
	    )
      | ZR_BRANCH(fs, ss) ->
	  let cl'' = buc_elim_exists (mi+1) ma fs bran in
	    if (cl'' = empty_set) then empty_set
	    else (
	      backtracks := !backtracks+1;
	      buc_elim_exists (mi+1) ma ss bran
	    )
  and compress_clause_set s bran = 
    let sizes = clause_set_size s in
    let rec compress_clause_set_int s ss bran =
      match bran with
	  [] -> s
	| hd::tl -> let (t,f,n) = split_subset (hd/2) s in
	  let s' = subsumption_free_union (subsumption_free_union t f) n in
	  let s'' = clause_distribution (build_clause [hd]) s' in
	  let sizes'' = clause_set_size s'' in
	    if (sizes''*4>ss) then
	      compress_clause_set_int s'' ss tl
	    else
	      s''
    in
      compress_clause_set_int s sizes bran
  and resolve_var_prop i s bran =
    if !debug_dump then (
      print_int (clause_set_size s);
      print_string "->";
      flush_all ()) else ();
    let (st, sf, sn) = split_subset i s in
    let sizet = clause_set_size st in
    let sizef = clause_set_size sf in
(*    let (st, sf, sn) = 
      if (!use_learning & (sizet>1000) & (sizef>1000)) then (
	let s' = compress_clause_set s bran in
	let (st, sf, sn) = split_subset i s' in
	(st, sf, sn)
      ) else (
	(st, sf, sn)
      )
    in*)
      if !debug_dump then (print_int (clause_set_size st);
			  print_string " ";
			  print_int (clause_set_size sf);
			  print_string " ";
			  print_int (clause_set_size sn);
			  print_string "->";
			  flush_all () ) else ();
      if (!always_split & (sizet>1) & (sizef>1)) or (!use_split & (sizet> !split_threshold) & (sizef> !split_threshold)) then (
	if (!use_learning & ((clause_set_size sn)<(int_of_float ((float_of_int (sizet+sizef))*. !learn_threshold)))) then (
(*	  if !debug_dump then (print_string "Splitting with learning") else ();*)
	  (*print_string "Splitting with learning";
	  flush_all();*)
	  let st = clause_distribution st (build_clause [i]) in
	  let sf = clause_distribution sf (build_clause [-i]) in
	  let (x,y,t) = if sizet > sizef then (sf, st,i*2+1) else (st, sf,i*2) in
(*	  let sn' = if ((clause_set_size sn) < sizet) then
	    clause_distribution sn (build_clause [(if sizet>sizef then (i*2) else (i*2+1))])
	  else
	    sn in*)
	  let fs = subsumption_free_union x sn in
	  let ss = subsumption_free_union y sn in
	    raise(ZR_BRANCH_LEARNING (fs, ss, t))
	) else (
	  if !debug_dump then (print_string "Splitting ") else ();
	  (*print_string "Splitting";
	  flush_all();*)
	  let (x,y,t) = if sizet > sizef then (sf, st,i*2+1) else (st, sf,i*2) in
	  let fs = subsumption_free_union x sn in
	  let ss = subsumption_free_union y sn in
	    raise (ZR_BRANCH (fs, ss))
	)
      ) else (
	let s' = clause_distribution st sf in
	  if !debug_dump then (  print_int (clause_set_size s');
				print_string "^";
				flush_all () ) else ();
	  let w = subsumption_free_union sn s' in
	  let b = match bran with
	      [] -> -1
	    | hd::tl -> hd
	  in
	  let w' = 
	    if !use_pure & !use_unit then (
	      simp_pure_unit w b
	    ) 
	    else if !use_pure then (
	      simp_pure w b
	    )
	    else if !use_unit then (
	      simp_unit w b
	    )
	    else
	      w
	  in
	    w'
      )
  in
  let mi = List.fold_left min vmax q in
  let ma = List.fold_left max 0 q in
    buc_elim_exists mi ma cl []

let compute_width cl = 
  let rec splitted_support l cl =
    if cl = empty_set || cl = empty_clause then
      l
    else
      let x = (zdd_var cl) in
      let t = zdd_t cl in
      let e = zdd_e cl in
	if e = empty_set || e = empty_clause then
	  (IntSet.add (x/2) (vars_support t))::l
	else
	  if ((zdd_var e)/2) = (x/2) then
	    splitted_support ((IntSet.add (x/2) (IntSet.union (vars_support t) (vars_support (zdd_t e))))::l) (zdd_e e)
	  else
	    splitted_support ((IntSet.add (x/2) (vars_support t))::l) e
  in
  let l = splitted_support [] cl in
  let l' = List.map IntSet.cardinal l in
  let rec get_width m hd l =
    match l with
	[] -> m
      | hd'::tl -> let ul = List.fold_left IntSet.union IntSet.empty l in
	let hd'' = IntSet.union (IntSet.inter hd ul) hd' in
	let _ = if !print_active then (
	  print_int_list (IntSet.elements hd'');
	  print_string "\n";
	  ()
	) else () in
	let m' = max m (IntSet.cardinal hd'') in
	  get_width m' hd'' tl
  in
    get_width 0 IntSet.empty l

let qbf_cnf_zr f = 
  let g = sort_quant_occurance_new f in
    report_time "Order ";
    dump_time "ordertime.dat" false;
    flush_all ();
(*    print_cnf_qbf g;*)
  let (f',q') = prenex_noshare_split g in
(*  let q'' = sort_quantifiers q' in*)
  let q = List.rev_append q' [] in
  let vmax = props f in
(*  let cl = make_clause_set f in*)
  let rec make_clause l var = 
    let rec strip l var = 
      match l with
	  [] -> (false, [], [])
	| hd::tl -> match hd with
	      x::tl' when x=var -> let (res, y,z) = strip tl var in if tl' = [] then (true, [] , z) else if res then (true, [], z) else (res, tl'::y,z)
	    | _ -> (false, [], l)
    in
    let (w,x,y) = strip l var in
(*      print_string "called for";
      List.map (fun x -> print_int_list x;
      print_string "\n") l;
      print_string "x=";
      List.map (fun x -> print_int_list x;
      print_string "\n") x;
      print_string "y=";
      List.map (fun x -> print_int_list x;
      print_string "\n") y;
*)
    let yz = if y = [] then empty_set else make_clause y (var+1) in
    let xz = if x = [] then if w then empty_clause else empty_set else make_clause x (var+1) in
(*    let xz' = change xz var in*)
      getzdd var xz yz
  in
(*  let make_clause c cl =
    let make_lits l cl =
      let l' = List.map (fun g -> match g with 
			     `Prop(v) -> v
			   | `Not(`Prop(v)) -> (-v)
			   | _ -> raise Bad_formula
			) l in    
	subsumption_free_union (build_clause l') cl
    in
    match c with
      |	`Or(l) -> make_lits l cl
      | `Prop(v) -> make_lits [c] cl
      | `Not(`Prop(v)) -> make_lits [c] cl
      | _ -> raise Bad_formula
  in*)
  let make_lits l =
    let l' = List.map (fun x -> match x with
			   `Prop(v) -> (v-1)*2
			 | `Not(`Prop(v)) -> (v-1)*2+1
			 | _ -> raise Bad_formula
		      ) l in
      List.sort Pervasives.compare l'
  in
  let sort_clauses l =
    let rec compare_list x y =
      match x with
	  [] -> -1
	| hd::tl -> match y with
	      [] -> 1
	    | hd'::tl' -> let z = Pervasives.compare hd hd' in
		if z <> 0 then z else compare_list tl tl'
    in
    let l' = List.sort compare_list l in
      l'
  in
  let f'' = match f' with
      `And(l) -> sort_clauses (List.map (fun x -> match x with
					     `Or(l) -> make_lits l
					   | `Prop(v) -> make_lits [x]
					   | `Not(`Prop(v)) -> make_lits [x]
					   | _ -> raise Bad_formula
					) l
			      )
    | _ -> raise Bad_formula
  in 
  let cl = make_clause f'' 0 in
(*  let cl = make_clause_set_fast f' sort_clauses in*)
(*  let cl = make_clause_set_fast_recursive f' in*)
(*  let cl'' = unit_prop cl' in*)
(*  let cl = prop_bdr cl' vmax 1000 in*)
(*  let _ = print_clauses cl in*)
    report_time "Clause set ";
    flush_all ();
    setbddvars vmax;
    match q with
	[] -> print_string "What?";
	  empty_set
      |	[(`Exists, qq)] -> (
	  match !alg with
	      Resolution -> 
		let cl' = bucket_elim_zres qq cl vmax in
		  cl'
	    | REMOVEUNWIT -> 
		let assignments = make_all_assignments 1 vmax in
		let a' = remove_unwitnessed_assignments cl assignments in
		  if a' = empty_set then
		    empty_clause
		  else
		    empty_set
	    | BDD ->
		let b = bddquantinv cl in
		  if b = bdd_zero then empty_clause else empty_set
	    | COMPUTEWIDTH ->
		let w = compute_width cl in
		  Printf.printf "width2 = %d\n" w;
		  dump_time_raw "width2.dat" 0 w;
		  flush_all ();
		  exit 0;
		  empty_clause
	    | BDDBUCKET ->
		let b = bddquant cl in
		  if b = bdd_zero then empty_clause else empty_set
	    | BDDNEXT ->
		let b = bddquantnext cl in
		  if b = bdd_zero then empty_clause else empty_set
	    | BDDSCHED ->
		let b = bddquantnew cl in
		  if b = bdd_zero then empty_clause else empty_set
	    | BDDALLQUANT ->
		let b = bddallquant cl in
		  if b = bdd_zero then empty_clause else empty_set
(*	    | BED ->
		let _ = bed_init (256*1024*1024) (64*1024*1024) in
		let b = bddallquantbed cl in
		  if b = bdd_zero then empty_clause else empty_set*)
	    | BDDNOQUANT ->
		let b = bddnoquant cl in
		  if b = bdd_zero then empty_clause else empty_set
	    | CNF2DNF ->
		let vf = (props f) + 1 in
		let b = cnf2dnf cl vf in
		  if b = bdd_zero then empty_clause else empty_set
	    | ZDDQUANT -> 
		let cl' = zddquant cl in
		  cl'
	)
      | _ -> empty_set
      
let qdd name = 
  let f = parse_dimacs name in
  let f' = build_prop_quants f in
  let f'' = simplify f' in
    try
      let d = qbf_cnf_zr f'' in
	if d = empty_set then
	  true
	else
	  false
    with x ->
      match x with
	  ZR_UNSAT -> false
	| ZR_SAT -> true
	| _ -> raise x
	  
let main () = 
  try
    Gc.set{ (Gc.get()) with Gc.minor_heap_size=512*1024 };
    Gc.set{ (Gc.get()) with Gc.major_heap_increment=2048*1024 };
    Gc.set{ (Gc.get()) with Gc.space_overhead = 90 };
    let name_index = ref 1 in
    let skip = ref false in
    let _ = is_qbf := false in
    for i = 1 to Array.length Sys.argv - 1 do
      if (!skip) then 
	skip := false
      else ( 
	if Sys.argv.(i) = "-p" then 
	  use_pure := true
	else if Sys.argv.(i) = "-p-" then 
	  use_pure := false
	else if Sys.argv.(i) = "-u" then 
	  use_unit := true
	else if Sys.argv.(i) = "-u-" then 
	  use_unit := false
	else if Sys.argv.(i) = "-s" then 
	  use_split := true
	else if Sys.argv.(i) = "-s-" then 
	  use_split := false
	else if Sys.argv.(i) = "-l" then 
	  use_learning := true
	else if Sys.argv.(i) = "-l-" then 
	  use_learning := false
	else if Sys.argv.(i) = "-d" then 
	  debug_dump := true
	else if Sys.argv.(i) = "-d-" then 
	  debug_dump := false
	else if Sys.argv.(i) = "-x" then 
	  always_split := true
	else if Sys.argv.(i) = "-x-" then 
	  always_split := false
	else if Sys.argv.(i) = "-v" then 
	  sort_alg := Diversity
	else if Sys.argv.(i) = "-c" then 
	  sort_alg := Cardinality
	else if Sys.argv.(i) = "-qo" then (
	  skip := true;
	  match Sys.argv.(i+1) with
	      "degree" -> sort_alg := Degree
	    | "diversity" -> sort_alg := Diversity
	    | "cardinality" -> sort_alg := Cardinality
	    | "bfs" -> sort_alg := BFS
	    | "bfsmin" -> sort_alg := BFSMIN
	    | "mcs" -> sort_alg := MCS
	    | "miw" -> sort_alg := MIW
	    | "mf" -> sort_alg := MF
	    | "new" -> sort_alg := NEW
	    | "none" -> sort_alg := None
	) else if Sys.argv.(i) = "-inv" then 
	  invert_order := true 
	else if Sys.argv.(i) = "-invb" then (
	  invertbdd ();
	) else if Sys.argv.(i) = "-minv" then (
	  Rgl.Graph.set_secondary_tiebreaker (1);
	) else if Sys.argv.(i) = "-maxv" then (
	  Rgl.Graph.set_secondary_tiebreaker (-1);
	) else if Sys.argv.(i) = "-min" then (
	  min_degree_on_card := true;
	  Rgl.Graph.set_order_tiebreaker (-1);
	) else if Sys.argv.(i) = "-notie" then (
	  Rgl.Graph.set_order_tiebreaker 0;
	) else if Sys.argv.(i) = "-mincs" then (
	  Rgl.Graph.set_order_sign (-1);
	) else if Sys.argv.(i) = "-fw" then
	  Rgl.Graph.set_width_min_degree_heuristic ()
        else if Sys.argv.(i) = "-f" then 
	  alg := CNF2DNF
	else if Sys.argv.(i) = "-w" then 
	  alg := REMOVEUNWIT
	else if Sys.argv.(i) = "-b" then 
	  alg := BDD
	else if Sys.argv.(i) = "-B" then 
	  alg := BDDALLQUANT
	else if Sys.argv.(i) = "-bb" then 
	  alg := BDDBUCKET
	else if Sys.argv.(i) = "-bn" then 
	  alg := BDDNEXT
	else if Sys.argv.(i) = "-bq" then 
	  alg := BDDSCHED
	else if Sys.argv.(i) = "-bz" then 
	  alg := ZDDQUANT
(*	else if Sys.argv.(i) = "-be" then 
	  alg := BED*)
	else if Sys.argv.(i) = "-bbb" then 
	  alg := BDDNOQUANT
	else if Sys.argv.(i) = "-cwb" then
	  alg := COMPUTEWIDTH
	else if Sys.argv.(i) = "-n" then 
	  sort_alg := None
	else if Sys.argv.(i) = "-noquant" then
	  set_no_quantification ()
	else if Sys.argv.(i) = "-width" then (
	  print_active_vars ();
	) else if Sys.argv.(i) = "-st" then (
	  split_threshold := int_of_string Sys.argv.(i+1);
	  skip := true;
	) else if Sys.argv.(i) = "-lt" then (
	  learn_threshold := float_of_string Sys.argv.(i+1);
	  skip := true;
	) else if Sys.argv.(i) = "-to" then (
	  let x = int_of_string Sys.argv.(i+1) in
	  let _ = update_time_limit x in
	    skip := true;
	)
	else
	  name_index := i;
      )
    done;
      let res = qdd Sys.argv.(!name_index) in
	report_time "Total ";
	dump_time "time.dat" res;
	dump_time_raw "de.dat" 0 !backtracks;
	print_string "back tracks = ";
	print_int !backtracks;
	print_string "\n";
	if res then
	  print_string "SAT\n"
	else
	  print_string "UNSAT\n";
	flush_all () ;
(*	bdd_info ();*)
	Gc.major ();
	exit 0;
  with x -> (
    match x with
	BDD_SpaceOut -> (
	  dump_time_raw "time.dat" (-2) 999999;
	  dump_time_raw "de.dat" 0 999999
	)
      | BDD_TimeOut -> (
	  dump_time_raw "time.dat" (-1) 999999;
	  dump_time_raw "de.dat" 0 999999
	)
      | _ -> (
	  dump_time_raw "time.dat" (-4) 999999;
	  dump_time_raw "de.dat" 0 999999
	)
  );
    exit (-2);;    

main();;








