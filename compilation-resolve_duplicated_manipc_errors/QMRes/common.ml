open Unix

module Int = 
  struct
    type t = int
    let compare = Pervasives.compare
  end
module IntSet = Set.Make(Int)
module IntMap = Map.Make(Int)

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

let erase_from_list v l =
  List.filter (fun x -> if x=v then false else true) l

let rec print_int_list l =
  match l with
      [] -> ()
    | hd::tl -> print_int hd; print_string " "; print_int_list tl
