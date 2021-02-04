open Kformula
open Mlk

let print_dfg f =
  let rec print_dfg_int f =
    match f with
	True -> print_string "true"
      | False -> print_string "false"
      | Prop(i) -> print_string "p";print_int i
      | Not(g) -> print_string "not(";print_dfg_int g;print_string ")"
      | And(l) -> print_string "and(";print_list l;print_string ")"
      | Or(l) -> print_string "or(";print_list l;print_string ")"
      | Modal(ModalOp(Diamond, _), g) -> print_string"dia(r,";print_dfg_int g;print_string ")"
      | Modal(ModalOp(Box, _), g) -> print_string"box(r,";print_dfg_int g;print_string ")"
      | _ -> ()
  and print_list l =
    match l with
	[] -> ()
      | [x] -> print_dfg_int x
      | hd::tl -> print_dfg_int hd;print_string ",";print_list tl
  in
  let print_props f =
    let rec print_props_int x max =
      let y = max-1 in
      if (x=y) then (
	print_string "(p";print_int x;print_string ",0)"
      ) else (
	print_string "(p";print_int x;print_string ",0),";print_props_int (x+1) max
      )
    in
    let i = propositions f in
      print_props_int 0 i
  in
    print_string "begin_problem(a).\nlist_of_descriptions.\nname({*a*}).\nauthor({*a*}).\nstatus(unknown).\ndescription({*a*}).\nend_of_list.\nlist_of_symbols.\n";
    print_string "predicates[(R,2),(r,0),";
    print_props f;
    print_string "].\n";
    print_string "end_of_list.\n";
    print_string "list_of_special_formulae(conjectures,EML).\nprop_formula(not(";
    print_dfg_int f;
    print_string ")).\nend_of_list.\nend_problem.\n"
    
let main () =
  Gc.set{ (Gc.get()) with Gc.minor_heap_size=512*1024 };
  Gc.set{ (Gc.get()) with Gc.major_heap_increment=2048*1024 };
  Gc.set{ (Gc.get()) with Gc.space_overhead = 90 };
  let name = Sys.argv.(1) in
  let f = load_k name in
  let f' = flatten f in
    print_dfg f';;

main();;
