open Common
open Cudd

type bed

type bed_op = BED_ITE | BED_K0 | BED_PI1 | BED_PI2 | BED_NOR | BED_NLIMP | BED_NPI1 | BED_NIMP | BED_NPI2 | BED_XOR | BED_NAND | BED_AND | BED_BIIMP | BED_IMP | BED_LIMP | BED_OR | BED_K1 | BED_EXISTS | BED_FORALL | BED_SUBST | BED_ESUB

external bed_init : int -> int -> unit = "ml_bed_init"
external bed_done : unit -> unit = "ml_bed_done"
external bed_mk : int -> bed_op -> bed -> bed -> bed = "ml_bed_mk"
external bed_upone : int -> bed -> bed = "ml_bed_upone"
external bed_upall : bed -> bed = "ml_bed_upall"
external bed_apply : bed_op -> bed -> bed -> bed = "ml_bed_apply"
external bed_is_reachable : bed -> bed -> bool = "ml_bed_is_reachable"
external bed_is_bdd : bed -> bool = "ml_bed_is_bdd"
external bed_size : bed -> int = "ml_bed_node_count"

external bed_get_one : unit -> bed = "ml_bed_get_one"
external bed_get_zero : unit -> bed = "ml_bed_get_zero"

external bed_l : bed -> bed = "ml_bed_get_low"
external bed_h : bed -> bed = "ml_bed_get_high"
external bed_v : bed -> int = "ml_bed_get_var"
external bed_o : bed -> bed_op = "ml_bed_get_op"

external bdd_to_bed : bdd -> bed = "ml_bdd_to_bed"
external bed_to_bdd : bed -> bdd = "ml_bed_to_bdd"

let bed_one = bed_get_one ()
let bed_zero = bed_get_zero ()

let bed_mk_op op l h = bed_mk 0 op l h
let bed_mk_var v l h = bed_mk v BED_ITE l h

