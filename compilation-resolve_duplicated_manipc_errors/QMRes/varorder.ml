open Common
open Options
open Qbfformula
open Qbf
open Heap
open Graph
open Zres

module Graph = BaseUndirectedGraph
module MinDegree = VertexOrderMinDegree(Graph)
module MaxCardinality = VertexOrderMaxCardinality(Graph)
module LayeredMaxCardinality = VertexOrderLayeredMaxCardinality(Graph)

let var_dd_order = ref [0]

let lit f = 
  match f with
      `Prop(v) -> v
    | `Not(`Prop(v)) -> -v
    | _ -> 0

let var l = if l>0 then l-1 else (-l)-1
let variable f = var (lit f)

let build_var_interaction_graph f =
  if !debug_varorder > 1 then
    print f;
  let pf = props f in
  let (f,q) = prenex_noshare_split f in
  let g = Graph.empty in
  let g = Graph.resize g pf in
  let rec build_var_interaction_graph_int f =
    let rec add_clique l = 
      match l with
	  [] -> ()
	| hd::tl -> let _ = Graph.connect g hd hd in
	    let _ = List.map (fun x -> Graph.connect g hd x) tl in 
	    add_clique tl
    in
    let vars l = List.map variable l in
      match f with
	  `And(l) -> let _ = List.map build_var_interaction_graph_int l in ()
	| `Or(l) -> add_clique (vars l)
	| _ -> ()
  in
  let _ = build_var_interaction_graph_int f in
    g

let build_rgl_var_interaction_graph f =
  let pf = props f in
  let (f,q) = prenex_noshare_split f in
  let g = Rgl.Graph.init pf in
  let rec add_self_loop x =
    if x<pf then (
      Rgl.Graph.add_edge g x x;
      add_self_loop (x+1)
    ) else ()
  in
  let _ = add_self_loop 0 in
  let rec build_var_interaction_graph_int f =
    let rec add_clique l = 
      match l with
	  [] -> ()
	| hd::tl ->
	    let _ = List.map (fun x -> Rgl.Graph.add_edge g hd x) tl in 
	    add_clique tl
    in
    let vars l = List.map variable l in
      match f with
	  `And(l) -> let _ = List.map build_var_interaction_graph_int l in ()
	| `Or(l) -> add_clique (vars l)
	| _ -> ()
  in
  let _ = build_var_interaction_graph_int f in
    g

let sort_rgl g = 
  match !sort_alg with
      BFS ->  Rgl.Graph.lex_bfs g
    | BFSMIN ->  Rgl.Graph.lex_bfs_min g
    | MCS ->  Rgl.Graph.mcs g
    | MIW ->  Rgl.Graph.min_induced_width g
    | MF ->  Rgl.Graph.min_fill g
    | NEW -> Rgl.Graph.new_alg g

let list_prefix l len =
  let rec lp_int l len l' = 
    match len with
	0 -> l'
      | _ -> let (hd::tl) = l in
	  lp_int tl (len-1) (l'@[hd])
  in
    lp_int l len []

let get_width f vl = 
  let g = build_rgl_var_interaction_graph f in
  let w = Rgl.Graph.width g vl in
    w

let clean f =
  let pf = props f in
  let (f',q) = prenex_noshare_split f in
  let vm = Array.make (pf+1) 0 in
  let rec make_vm q i =
    let rec make_vm_int qq i = 
      match qq with
	  [] -> i
	| hd::tl -> (
	    if (!Options.debug_varorder > 0) then (
	      Printf.printf "mapping %d to %d\n" hd i;
	    );
	    vm.(hd) <- i; 
	    make_vm_int tl (i+1)
	  )
    in
    match q with
	[] -> i
      | (_,hd)::tl -> let i' = make_vm_int hd i in make_vm tl i'
  in
  let _ = make_vm q 1 in
  let f' = map_vars vm f in
  let _ = if (!Options.debug_varorder > 0) then (
    Printf.printf "Cleaned Formula\n";
    print f'; ()
  ) in
    f'

let sort_rgl_level_qbf_old f =
  let pf = props f in
  let (f',q) = prenex_noshare_split f in
  let q' = List.rev (List.map (fun x -> let (_,x') = x in x') q) in
  let rec sort_rgl_level_int f q vo = 
    match q with
	[] -> vo
      | hd::tl ->
	  let vars = List.flatten q in
	  let vset = List.fold_left (fun s x -> IntSet.add x s) IntSet.empty vars in 
	  let pf' = List.length vars in
	  let vti = Array.make (pf+1) 0 in
	  let itv = Array.make (pf'+1) 0 in
	  let g = Rgl.Graph.init pf' in
	  let rec add_clique l = 
	    match l with
		[] -> ()
	      | hd::tl ->
		  let _ = List.map (fun x -> Rgl.Graph.add_edge g hd x) tl in 
		    add_clique tl
	  in
	  let _ = List.fold_left (fun i x -> vti.(x)<-i; itv.(i)<-x; (i+1)) 0 vars in 
	  let vars l = List.map variable l in
	  let rec build_var_interaction_graph_int f =
	    match f with
		`And(l) -> let _ = List.map build_var_interaction_graph_int l in ()
	      | `Or(l) -> add_clique (List.map (fun x -> vti.(x)) (List.filter (fun x -> IntSet.mem x vset) (vars l)))
	      | _ -> ()
	  in
	  let _ = build_var_interaction_graph_int f' in
	  let vo' = 
	    match tl with
		[] -> let vo2 = sort_rgl g in
		  vo @ (List.map (fun x -> itv.(x)) vo2)
	      | _ ->
		  let vv = List.map (fun x -> vti.(x)) (List.flatten tl) in
		  let _ = add_clique vv in
		  let vo1 = sort_rgl g in
		  let g' = Rgl.Graph.build_tree_decomposition g vo1 in
		  let vo2 = Rgl.Graph.reroot_tree_decomposition g' vv in
		  let vo3 = List.map (fun x -> itv.(x)) (list_prefix vo2 (List.length hd)) in
		    vo @ vo3
	  in
	    sort_rgl_level_int f tl vo'
  in
  let vo = sort_rgl_level_int f' q' [] in
  let vo' = List.map (fun i -> i-1) vo in
  let width = get_width f' vo' in
    Printf.printf "width = %d\n" width;
    dump_time_raw "width.dat" 0 width;
    flush_all ();
    vo'

let sort_rgl_level_qbf f =
  let pf = props f in
    Printf.printf "Props = %d\n" pf;
  let (f',q) = prenex_noshare_split f in
  let g = Rgl.Graph.init pf in
  let rec add_clique l = 
    match l with
	[] -> ()
      | hd::tl ->
	  let _ = List.map (fun x -> Rgl.Graph.add_edge g hd x) tl in 
	    add_clique tl
  in
  let rec build_var_interaction_graph_int f =
    let vars l = List.map variable l in
    match f with
	`And(l) -> let _ = List.map build_var_interaction_graph_int l in ()
      | `Or(l) -> add_clique (vars l)
      | _ -> ()
  in
  let mark_tags q pf =
    let l = Array.make pf 0 in
    let rec mark_level q lev = 
      match q with
	  [] -> ()
	| hd::tl -> (
	    let (_,vars) = hd in
	      if (!invert_order) then
		List.map (fun x -> l.(x-1) <- ((100-lev)*65536)) vars
	      else
		List.map (fun x -> l.(x-1) <- (lev*65536)) vars;
	      mark_level tl (lev+1)
	  )
    in
      mark_level q 1;
      Array.mapi (fun i x -> Rgl.Graph.associate_vertex g i x) l
  in
  let _ = if (!Options.unified_vo) then () else (mark_tags q pf; ()) in
  let _ = build_var_interaction_graph_int f' in
  let vo = Rgl.Graph.mcs_layered g in
    Printf.printf "Build done\n";
    flush_all ();
  let _ = if !quiet_output then () else (
    let width = Rgl.Graph.width g vo in
      Printf.printf "width = %d\n" width;
      dump_time_raw "width.dat" 0 width;
      flush_all ();
      ()
  ) in
    vo

let varorder_handle_shuffle f ro = 
  let pf = props f in
  let g = Rgl.Graph.init pf in
(*  let _ = Options.use_unit := false in*)
  let rec add_clique l = 
    match l with
	[] -> ()
      | hd::tl ->
	  let _ = List.map (fun x -> Rgl.Graph.add_edge g hd x) tl in 
	    add_clique tl
  in
  let rec build_var_interaction_graph_int f =
    let vars l = List.map variable l in
    match f with
	`And(l) -> let _ = List.map build_var_interaction_graph_int l in ()
      | `Or(l) -> add_clique (vars l)
      | _ -> ()
  in
  let _ = build_var_interaction_graph_int f in
  let _ = if (!Options.dd_order = Hybrid) then 
    Rgl.Graph.triangulate g ro else 0 
  in 
  let vo = Rgl.Graph.mcs g in
(*  let vo = Rgl.Graph.sift_graph_width g (pf*100) vo in*)
  let _ = var_dd_order := vo in
  let width = Rgl.Graph.width g vo in
  let vmax =  List.fold_left max 0 vo in
  let _ = setbddvars (vmax+1) in
  let _ = Printf.printf "Start shuffling\n" in
  let _ = flush_all () in
  let _ = shuffleheap vo in
    Printf.printf "width = %d\n" width;
    dump_time_raw "width.dat" 0 width;
    flush_all ();
    ()

let sort_degree f = 
  let vo = MinDegree.init (build_var_interaction_graph f) in
  let l = MinDegree.sort vo in
  let _ = MinDegree.shutdown vo in
    l
and sort_cardinality f = 
  let vo = MaxCardinality.init (build_var_interaction_graph f) in
  let l = MaxCardinality.sort vo in
  let _ = MaxCardinality.shutdown vo in
    l
and sort_layered_cardinality f =
  let g = build_var_interaction_graph f in
  let (f',q) = prenex_noshare_split f in
  let q' = List.rev (List.map (fun (qt,ql) -> ql) q) in
  let l = LayeredMaxCardinality.sort g q' in
    l
and sort_diversity f =
  let (f',q) = prenex_noshare_split f in
  let vf = props f in
  let diversity = Array.init (vf+1) (fun i -> (i,0,0)) in
  let rec count_diversity f =
    let count_lits l = let _ = List.map 
				 (fun f -> 
				    let l = lit f in
				    let v = var l in
				      Printf.printf "%d " v;
				    let (ll,p,n) = diversity.(v) in
				      if l<0 then diversity.(v) <- (ll,p,n+1)
				      else diversity.(v) <- (ll,p+1,n)
				 ) l in ()
    in
      match f' with
	  `And(l) -> let _ = List.map count_diversity l in ()
	| `Or(l) -> count_lits l
	| _ -> ()
  in
  let _ = count_diversity f in
  let _ = Array.sort (fun (a1,a2,a3) (b1,b2,b3) -> Pervasives.compare (a2*a3) (b2*b3)) diversity in
    Array.to_list (Array.map (fun (a,b,c) -> a) diversity)
and sort_none f =
  let (f',q) = prenex_noshare_split f in
    List.sort Pervasives.compare (List.fold_left (fun l (qt,qq) -> l @ qq) q [])
and sort_rgl_lex f = 
  let g = build_rgl_var_interaction_graph f in
  let vl = Rgl.Graph.lex_bfs g in
    vl
and sort_rgl_lex_min f = 
  let g = build_rgl_var_interaction_graph f in
  let vl = Rgl.Graph.lex_bfs_min g in
    vl
and sort_rgl_mcs f = 
  let g = build_rgl_var_interaction_graph f in
  let vl = Rgl.Graph.mcs g in
    vl
and sort_rgl_formula f = 
  let g = build_rgl_var_interaction_graph f in
  let vl = sort_rgl g in
    vl

let get_width f vl = 
  let g = build_rgl_var_interaction_graph f in
  let w = Rgl.Graph.width g vl in
    w

let print_quantifier_map qm = 
  print_string "Quantifier Map is\n";
  Array.iter (fun x -> Printf.printf "%d " x) qm;
  print_string "\n"
      
let make_quantifier_map q vf = 
  let qm = Array.make (vf+1) 0 in
  let rec make_qm_int q lev = 
    let rec make_qm_int2 q lev = 
      let _ = List.map (fun i -> qm.(i) <- lev) q in () 
    in
    let _ = List.fold_left (fun i (qt, qv) -> let _ = make_qm_int2 qv i in (i+1)) lev q in ()
  in
  let _ = ( match q with
		[] -> ()
	      | (`Exists,_)::_ -> let _ = make_qm_int q 1 in ()
	      | _ -> make_qm_int q 2 ) in
(*    print_quantifier_map qm;*)
    qm

let make_resolution_order qm =
  match !qo_alg with
      ExistBeforeUniv | Arbitary -> 
	let (v,l) = Array.fold_left (fun (i,l) lev -> if (lev mod 2)=1 then (i+1,i::l) else (i+1,l)) (0,[]) qm in
	  List.rev l
    | Layered ->
	(*Layered order does not search for universal literals, they request quaitification of them*)
	let m = Array.mapi (fun i a -> (i,a)) qm in
	let m' = Array.sub m 1 ((Array.length qm)-1) in
	let _ = Array.stable_sort (fun (v1,a1) (v2,a2) -> -(compare a1 a2)) m' in
	let (l,_) = List.split (Array.to_list m') in
	  l

let make_layered_branch_order f = 
  let g = build_var_interaction_graph f in
  let (f',q) = prenex_noshare_split f in
  let q' = List.map (fun (qt,ql) -> ql) q in
  let l = LayeredMaxCardinality.sort g q' in
    l  

let order_quant_vars vo f =
  let vf = props f in
  let m = Array.make (vf+1) 0 in
  let _ = List.fold_left (fun i v -> m.(v+1) <- i; i+1) 1 vo in
  let f'' = map_vars m f in
    f''

let sort_branching_vars bo g = 
  let (bt, bl) = List.split bo in
  let (sbl,_) = LayeredMaxCardinality.sort_ g bl [] IntSet.empty in
    List.combine bt sbl

let make_layered_resolution_order f =
  let vo = sort_rgl_level_qbf f in
  let (f',q) = prenex_noshare_split f in
  let q' = List.rev q in
  let q'' = List.map (fun (_,x) -> x) q' in
    List.flatten q''

let sort_vars ff =
  let f = clean ff in
  let sorted f = 
    let vo' = match !sort_alg with
	Diversity -> sort_diversity f
      | Degree -> sort_degree f
      | Cardinality -> sort_cardinality f
      | LayeredCardinality -> sort_layered_cardinality f
      | None -> IntSet.elements (support_vars f)
      | BFS | BFSMIN | MCS | MIW | MF |NEW -> 
	  if !vo_alg = LayeredVO then
	    sort_rgl_level_qbf f
	  else (
	    match !sort_alg with
		BFS -> sort_rgl_lex f
	      | BFSMIN -> sort_rgl_lex_min f
	      | MCS -> sort_rgl_mcs f
	      | _ -> sort_rgl_formula f
	  )
    in
      if !quiet_output then () else Printf.printf "Invert is %s\n" (if !invert_order then "true" else "false");
    let vo = if !invert_order then (
      if !quiet_output then () else Printf.printf "Inverted VO\n";
      List.rev vo' 
    ) else vo' in
      if !qo_alg = ExistBeforeUniv then (
	let (f'',q) = prenex_noshare_split f in
	let vf = props f in
	let qm = make_quantifier_map q vf in
	let (vo',vo'') = List.partition (fun x -> qm.(x+1) mod 2 = 1) vo in
	  if !debug_varorder > 0 then (
	    print_string "splitted vo is ";
	    print_int_list (vo' @ vo'');
	  );
	  vo' @ vo''
      )
      else vo
  in
  let var_sorted = sorted f in
    if !debug_varorder > 0 then (
      print_int_list var_sorted;
      print_string "sorted \n";
      flush_all ();
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
  let vf = props f' in
  let _ = if !is_qbf && !quiet_output && vf > 32765 then (
    Printf.printf "Variable count exceeds CUDD bounds\n";
    exit 0
  ) else () in
    if !debug_varorder > 0 then
      Printf.printf "vf of simplied formula is %d\n" vf;
  let qm = make_quantifier_map q vf in
    if !debug_varorder > 1 then
      print_quantifier_map qm;
  let _ = set_quantifier_map qm in
  let ro = if (!vo_alg = UnifiedVO) && ((!sort_alg = BFS) || (!sort_alg = BFSMIN) || (!sort_alg = MCS)) then
    make_layered_resolution_order f'
  else
    make_resolution_order qm in
    if !debug_varorder > 0 then (
      Printf.printf "Resolution Order is\n";
      print_int_list ro;
      Printf.printf "Resolution Order done\n";
      flush_all ();
    );
  let bo = List.map (fun (a,b) -> if a = `Exists then (true,b) else (false,b)) q in
(*  let bo' = sort_branching_vars bo (build_var_interaction_graph f') in*)
    if (!quiet_output) then () else (
    report_time "Order ";
    dump_time "ordertime.dat" false;
    );
    (bo,ro,qm,f'')
