open Common
open Cudd

let test_basic () = 
  let d1 = bdd_var 2 in
  let d2 = bdd_not d1 in
  let d3 = bdd_and d1 d2 in
  let d4 = bdd_or d1 d2 in
  let one = bdd_one in
  let zero = bdd_zero in
  let x = bdd_size d2 in
    print_string "checking\nd2 size = ";
    print_int x;
    if (d3 = zero) then
      print_string "\nmult successful \n";
    if (d4 = one) then
      print_string "add successful \n";
    ()

let rec rand_bdd p s = 
  if (s = 1) then
    bdd_var (Random.int p)
  else
    let x = (Random.int (s-1)) + 1 in
    let x' = s-x in
    let op = Random.int 2 in
    let f = rand_bdd p x in
    let f' = rand_bdd p x' in
      if (op = 0) then
	bdd_and f f'
      else
	bdd_or f f'

let test_cube () =
  let f = rand_bdd 50 20 in
  let x = bdd_var_set f in
  let x' = IntSet.elements x in
  let _ = List.map (fun i -> print_int i;print_string " ") x' in
    print_int (bdd_size f);
    print_string "\n";    
    ()

let test () = 
  Random.self_init ();
  test_basic ();
  test_cube ();
  Gc.major ();;

test ();;
