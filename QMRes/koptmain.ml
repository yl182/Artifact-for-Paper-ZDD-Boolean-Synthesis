open Kformula
open Mlk
open Kopt

let main () =
  Gc.set{ (Gc.get()) with Gc.minor_heap_size=512*1024 };
  Gc.set{ (Gc.get()) with Gc.major_heap_increment=2048*1024 };
  Gc.set{ (Gc.get()) with Gc.space_overhead = 90 };
  let name = Sys.argv.(1) in
  let f = load_k name in
(*  let f = load_opt name in
  let i = propositions (load_k name) in
  let g = opt_all f in
  let h = unmap_prop_levels i g in *)
  let g = 
    if ((Array.length Sys.argv) >= 3) then
      if (Sys.argv.(2) = "-l") then
	optimize_k f false
      else
	optimize_k f true
    else
      optimize_k f true in
    print_lwb g;
    exit 0;;

main ();;
