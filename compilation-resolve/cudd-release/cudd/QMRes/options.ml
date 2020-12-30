
type sortalg = Degree | Diversity | Cardinality | LayeredCardinality| BFS| BFSMIN|MCS|MIW|MF|NEW| None
type qoalg = Layered | ExistBeforeUniv | Arbitary
type resalg = Resolution | BDD
type voalg = UnifiedVO | LayeredVO
let res_alg = ref Resolution
let sort_alg = ref MCS
let qo_alg = ref Layered
let split_threshold = ref 100000
let bdd_threshold = ref 50000
let backtracks = ref 0
let debug_level = ref 0
let use_split = ref false
let use_unit = ref true
let use_pure = ref false
let invert_order = ref false 
let splitting_score_threshold = ref 1.5
let debug_branching = ref 0
let debug_resolution = ref 0
let debug_varorder = ref 0
let debug_graph = ref 0
let vo_alg = ref LayeredVO
let zres_use_bdd = ref false
let zres_split_bdd = ref true
let is_qbf = ref true
let quiet_output = ref false
let unified_vo = ref true

let no_var_shuffle = ref true

let max_clauses = ref 0
let max_nodes = ref 0

let measure_size = ref false

type ddorder = Unified | Hybrid | Elimination

let dd_order = ref Elimination

let min_degree_on_card = ref false

let check_branching st sf = !use_split && st> !split_threshold && sf> !split_threshold

let check_bdd_branching size = !use_split && size > !split_threshold

let parse_options () = 
    let name_index = ref 1 in
    let skip = ref false in
    let _ = Rgl.Graph.set_width_min_degree_heuristic () in
      if !quiet_output then (
	if (Array.length Sys.argv) < 3 then
	  Cudd.set_timeout 1000
	else
	  Cudd.set_timeout (int_of_string Sys.argv.(2));
	Sys.argv.(1)
      ) else (
    for i = 1 to Array.length Sys.argv - 1 do
      if (!skip) then 
	skip := false
      else ( 
	if Sys.argv.(i) = "-s" then 
	  use_split := true
	else if Sys.argv.(i) = "-s-" then 
	  use_split := false
	else if Sys.argv.(i) = "-d" then ( 
	  debug_level := int_of_string Sys.argv.(i+1);
	  skip := true
	) else if Sys.argv.(i) = "-dr" then ( 
	  debug_resolution := int_of_string Sys.argv.(i+1);
	  skip := true
	) else if Sys.argv.(i) = "-bs" then ( 
	  bdd_threshold:= int_of_string Sys.argv.(i+1);
	  skip := true
	) else if Sys.argv.(i) = "-to" then ( 
	  Cudd.update_time_limit (int_of_string Sys.argv.(i+1));
	  skip := true
	) else if Sys.argv.(i) = "-v" then 
	  sort_alg := Diversity
	else if Sys.argv.(i) = "-c" then 
	  sort_alg := Cardinality
	else if Sys.argv.(i) = "-g" then 
	  sort_alg := Degree
	else if Sys.argv.(i) = "-n" then 
	  sort_alg := None
	else if Sys.argv.(i) = "-uvo" then 
	  unified_vo := true
	else if Sys.argv.(i) = "-nonuvo" then 
	  unified_vo := false
	else if Sys.argv.(i) = "-layered" then 
	  vo_alg := LayeredVO
	else if Sys.argv.(i) = "-b" then (
	  res_alg := BDD;
	  split_threshold := 1000000;
	  use_pure := false
	) else if Sys.argv.(i) = "-qo" then (
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
	    | "none" -> sort_alg := None
	) else if Sys.argv.(i) = "-l" then 
	  sort_alg := LayeredCardinality
	else if Sys.argv.(i) = "-u" then
	  use_unit := true
	else if Sys.argv.(i) = "-u-" then
	  use_unit := false
	else if Sys.argv.(i) = "-p" then
	  use_pure := true
	else if Sys.argv.(i) = "-p-" then
	  use_pure := false
	else if Sys.argv.(i) = "-size" then
	  measure_size := true
	else if Sys.argv.(i) = "-zb" then
	  zres_use_bdd := true
	else if Sys.argv.(i) = "-zsn" then
	  zres_split_bdd := false
	else if Sys.argv.(i) = "-minw" then
	  Rgl.Graph.set_order_sign (-1)
	else if Sys.argv.(i) = "-inv" then
	  invert_order := true
	else if Sys.argv.(i) = "-min" then (
	  min_degree_on_card := true;
	  Rgl.Graph.set_order_tiebreaker (-1);
	) else if Sys.argv.(i) = "-vo" then (
	  Cudd.bdd_enable_reorder ();
	  Cudd.bdd_enable_reorder_report ();
	  Printf.printf "DVO enabled\n";
	) else if Sys.argv.(i) = "-qo" then (
	  skip := true;
	  match Sys.argv.(i+1) with
	      "layered" -> qo_alg := Layered
	    | "arbitary" -> qo_alg := Arbitary
	    | "existbeforeuniv" -> qo_alg := ExistBeforeUniv
	) else if Sys.argv.(i) = "-min" then (
	  min_degree_on_card := true;
	  Rgl.Graph.set_order_tiebreaker (-1);
	) else if Sys.argv.(i) = "-notie" then (
	  Rgl.Graph.set_order_tiebreaker 0;
	) else if Sys.argv.(i) = "-unified" then (
	  dd_order := Unified;
	) else if Sys.argv.(i) = "-hybrid" then (
	  dd_order := Hybrid;
	) else if Sys.argv.(i) = "-st" then (
	  split_threshold := int_of_string Sys.argv.(i+1);
	  skip := true;
	) else if Sys.argv.(i) = "-fastwidth" then (
	  Rgl.Graph.set_width_min_degree_heuristic ();
	) else
	  name_index := i;
      )
    done;
	Sys.argv.(!name_index)
      )
