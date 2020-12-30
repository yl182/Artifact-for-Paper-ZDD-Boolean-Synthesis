open Kformula
open Mlk

(*let main () = 
  let size = int_of_string Sys.argv.(1) in
  let props = int_of_string Sys.argv.(2) in
  let mtop = float_of_string Sys.argv.(3) in
  let bbias = float_of_string Sys.argv.(4) in
  let abias = float_of_string Sys.argv.(5) in
  let f = random_n size props mtop bbias abias in
    print_lwb f;
    exit 0;;
*)

let main () = 
  let l = float_of_string Sys.argv.(1) in
  let n = int_of_string Sys.argv.(2) in
  let c = float_of_string Sys.argv.(3) in
  let d = int_of_string Sys.argv.(4) in
  let p = float_of_string Sys.argv.(5) in
    Random.self_init();
  let f = random_cnf l n c 1 d p in
    print_lwb f;
    exit 0;;

main ();;

