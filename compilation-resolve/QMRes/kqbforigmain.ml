open Kqbf
open Kformula
open Mlk

let main () =
  Gc.set{ (Gc.get()) with Gc.minor_heap_size=512*1024 };
  Gc.set{ (Gc.get()) with Gc.major_heap_increment=2048*1024 };
  Gc.set{ (Gc.get()) with Gc.space_overhead = 90 };
  if (Array.length Sys.argv) <= 1 then (
    print_string "K to QBF translator. (C)Rice University.\n";
    print_string "Usage: kqbforig filename\n")
  else (
  let name = Sys.argv.(1) in
  let f = load_k name in
  let g = get_qbf f in
    Qbf.print g;
  );
    exit 0;;

main();;

