open Qbf
open Mlk
open Kopt
open Kqbf
open Cudd
open Unix
open Ddopt

let report_time s = 
  let t = times () in
    print_string s;
    print_float t.tms_utime;
    print_string "u ";
    print_float t.tms_stime;
    print_string "s\n"

let dump_time_raw fn res t = 
  let chan = open_out_gen [Open_wronly;Open_append;Open_creat;Open_text] 420 fn in
    output_string chan (string_of_int res);
    output_string chan ",";
    output_string chan (string_of_int t);
    close_out chan
      
let dump_time fn res = 
  let t = times () in
  let msecs = int_of_float (t.tms_utime *. 1000.0) in
  let res' = if (res) then 1 else 0 in
    dump_time_raw fn res' msecs

let timeout_handler sig_num =
  print_string "handler called\n";
  flush Pervasives.stdout;
  dump_time_raw "time.dat" (-1) 999999;
  exit (-1)

let rec make_dd f = 
  let d = 
    match f with
	`True -> bdd_one
      | `False -> bdd_zero
      | `Prop(i) -> bdd_var i
      | `Not(g) -> bdd_not (make_dd g)
      | `And(l) -> let l' = List.map make_dd l in
	 (* List.fold_right bdd_and l' bdd_one *)
	  list_op l' bdd_and bdd_one
      | `Or(l) -> let l' = List.map make_dd l in
	 (* List.fold_right bdd_or l' bdd_zero *)
	  list_op l' bdd_or bdd_zero
      | `Quant((`Exists, g), `And(l)) ->
	  let l' = List.map make_dd l in
	    and_exist_opt_bucket g l'
      | `Quant(q, g) -> let g' = make_dd g in
	let (t,qq) = q in
	let q' = bdd_makecube qq in
	  ( match t with
	      `Forall -> bdd_forall q' g'
	    | `Exists -> bdd_exists q' g'
	  )
      | _ -> bdd_zero
  in
    d
      
let test_dd f = 
  let d = make_dd f in
  if (d = bdd_zero) then
    false
  else
    true
    
let qkbdd () = 
  try
    let name = Sys.argv.(1) in
    let f = load_k name in
    let f' = optimize_k f true in
      report_time "OPT ";
      let f'' = get_qbf f' in
	report_time "QBF ";
	let f''' = shuffle_vars f'' in
	let result = test_dd f''' in
	  report_time "Total ";
	  dump_time "time.dat" result;
	  if (result) then
	    print_string "SAT\n"
	  else
	    print_string "UNSAT\n";
	  ()
  with x ->
    match x with
	BDD_SpaceOut -> dump_time_raw "time.dat" (-2) 999999
      | BDD_TimeOut -> dump_time_raw "time.dat" (-1) 999999
      | _ -> dump_time_raw "time.dat" (-4) 999999;
    exit (-2)

let main () = 
  Gc.set{ (Gc.get()) with Gc.minor_heap_size=512*1024 };
  Gc.set{ (Gc.get()) with Gc.major_heap_increment=2048*1024 };
  Gc.set{ (Gc.get()) with Gc.space_overhead = 90 };
(*  KQbf.use_one_hot_encoding = false;*)
(*  bdd_enable_reorder ();
  bdd_enable_reorder_report ();*)
(*  Sys.set_signal Sys.sigsegv (Sys.Signal_handle(timeout_handler));*)
  qkbdd ();
  Gc.minor ();
  Gc.major ();
  exit 0;;

main();;
