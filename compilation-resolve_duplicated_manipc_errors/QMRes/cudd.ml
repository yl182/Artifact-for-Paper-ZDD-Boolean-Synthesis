(** OCaml binding for Cudd-2.3.1 **)
open Common

type bdd

external bdd_init : unit -> unit = "bdd_init"
external bdd_info : unit -> unit = "bdd_info"
external bdd_get_one : unit -> bdd = "bdd_one"
external bdd_get_zero : unit -> bdd = "bdd_zero"
external bdd_var_int : int -> bdd = "bdd_var"
external bdd_not : bdd -> bdd = "bdd_not"
external bdd_and :  bdd -> bdd -> bdd = "bdd_and"
external bdd_or : bdd -> bdd -> bdd = "bdd_or"
external bdd_diff : bdd -> bdd -> bdd = "bdd_diff"
external bdd_exists : bdd -> bdd -> bdd = "bdd_exists"
external bdd_forall : bdd -> bdd -> bdd = "bdd_forall"
external bdd_andexist : bdd -> bdd -> bdd -> bdd = "bdd_andexist"
external bdd_support : bdd -> bdd = "bdd_support"

external bdd_underapprox : bdd -> int -> bdd = "bdd_underapprox"
external bdd_overapprox : bdd -> int -> bdd = "bdd_overapprox"

external bdd_constrain : bdd -> bdd -> bdd = "bdd_constrain"

external bdd_top : bdd -> int = "bdd_top"
external bdd_t : bdd -> bdd = "bdd_t"
external bdd_e : bdd -> bdd = "bdd_e"

external bdd_make_node : int -> bdd -> bdd -> bdd = "bdd_make_node"

external bdd_makecube : int list -> bdd = "bdd_makecube"
external bdd_size : bdd -> int = "bdd_size"

external bdd_enable_reorder : unit -> unit = "bdd_enable_reorder"
external bdd_disable_reorder : unit -> unit = "bdd_disable_reorder"
external bdd_enable_reorder_report : unit -> unit = "bdd_enable_reorder_report"
external bdd_disable_reorder_report : unit -> unit = "bdd_disable_reorder_report"

external bdd_total_vars : unit -> int = "bdd_total_vars"

external update_time_limit: int -> unit = "update_time_limit"
external set_timeout: int -> unit = "set_timeout"

let bdd_one = bdd_get_one ()
let bdd_zero = bdd_get_zero ()

exception BDD_SpaceOut
exception BDD_TimeOut
exception BDD_IndexTooBig

let spaceout_handler () =
  raise BDD_SpaceOut

let timeout_handler () = 
  raise BDD_TimeOut

let cudd_runtime_init = 
  let _ = Callback.register "ocaml_minor_gc" Gc.minor in
  let _ = Callback.register "ocaml_major_gc" Gc.major in
  let _ = Callback.register "ocaml_spaceout_handler" spaceout_handler in
  let _ = Callback.register "ocaml_timeout_handler" timeout_handler in
    bdd_init ()

let bdd_var i =
(*  if (i <= 65533) then*)
    bdd_var_int i
(*  else
    raise BDD_IndexTooBig*)
      
let bdd_is_terminal f = 
  if (f = bdd_one or f = bdd_zero) then
    true
  else
    false

let rec bdd_is_var_in_support f v =
(*WRONG  let v' = bdd_var v in
  let f' = bdd_and f v' in
    if (f' = bdd_zero) then false else true*)
  if (f = bdd_one or f = bdd_zero) then false
  else if ((bdd_top f) = v) then true
  else bdd_is_var_in_support (bdd_t f) v

let rec print_support f =
  if (f = bdd_one or f = bdd_zero) then ()
  else (
    print_int (bdd_top f);
    print_string " ";
    print_support (bdd_t f);
  )

let  is_var_used f v = 
  let f' = bdd_support f in
    bdd_is_var_in_support f' v

let rec bdd_var_set_cube f = 
  if (bdd_is_terminal f) then
    IntSet.empty
  else 
    IntSet.add (bdd_top f) (bdd_var_set_cube (bdd_t f))
and bdd_var_set f =
  bdd_var_set_cube (bdd_support f)
