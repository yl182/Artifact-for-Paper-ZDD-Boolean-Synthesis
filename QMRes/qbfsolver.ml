open Common
open Qbfformula
open Qbf
open Cudd
open Ddopt
open Zres
open Options
open Resolution
open Prioritizedresolution
open Unix

type sortalg = Degree | Diversity | Cardinality | None
let sort_alg = ref Diversity
let debug_dump = ref true
let split_threshold = ref 100
let use_splitting = ref true

exception Unknown_error

let check_satisfiability name = 
  let f = parse_dimacs name in
  let f' = match f with
      `Quant(_,_) -> f 
    | _ -> build_prop_quants f
  in
  let f'' = simplify f' in
  let d = qdd f'' in
    match d with
	Satisfied -> true
      | Unsatisfied -> false
      | _ -> raise Unknown_error
	  
let main () = 
  try
    Gc.set{ (Gc.get()) with Gc.minor_heap_size=512*1024 };
    Gc.set{ (Gc.get()) with Gc.major_heap_increment=2048*1024 };
    Gc.set{ (Gc.get()) with Gc.space_overhead = 90 };
    let name = parse_options () in
    let res = check_satisfiability name in
      report_time "Total ";
      let _ = if (!quiet_output) then () else (
	dump_time "time.dat" res;
	if (!Options.measure_size) then (
	  dump_time_raw "nodes.dat" 0 !max_nodes;
	  dump_time_raw "clauses.dat" 0 !max_clauses;
	) else ();
      ) in
      if res then (
	print_string "SAT\n";
	exit 10
      ) else (
	print_string "UNSAT\n";
	exit 20
      );
      flush_all () ;
      Gc.major ();
      exit 0;
  with x ->
    match x with
	Unknown_error -> print_string "Unknown answer. Error\n";
	  dump_time_raw "time.dat" (-3) 999999
      | BDD_SpaceOut -> if (!quiet_output) then (print_string "Spaced 
out\n") else (let _ = print_string "Spaced out\n" in dump_time_raw 
"time.dat" (-2) 999999)
      | BDD_TimeOut -> if (!quiet_output) then (print_string "Timed out\n") else (
	let _ = print_string "Timed out\n" in
	  dump_time_raw "time.dat" (-1) 999999)
      | _ -> if (!quiet_output) then () else (let _ = dump_time_raw "time.dat" (-4) 999999 in ());
	  exit (-2);;    

main();;

