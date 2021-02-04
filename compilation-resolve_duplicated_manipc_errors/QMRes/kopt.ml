open Kformula
open Mlk

let write_lwb form name =
  let outf = open_out name in
    Format.set_formatter_out_channel outf;
    print_lwb form

let opt_unroll_diamond form =
  let f' = flatten form in
  match f' with
      And( l ) -> flatten (
	let is_diamond i f =
	  match f with
	      Modal(ModalOp(Diamond, i), _) -> true
	    | _ -> false in
	let is_modal i f =
	  match f with
	      Modal(ModalOp(_, i), _) -> true
	    | _ -> false in
	let strip_modal_op f = 
	  match f with 
	      Modal(m, f) -> f
	    | _ -> Invalid in
	let count_or l = List.length (List.filter (fun f -> match f with Or(_) -> true | _ -> false ) l) in
	let count_diamond i l = List.length (List.filter (is_diamond i) l) in
	  if ((count_diamond 1 l) = 1) & ((count_or) l = 0) 
	  then let (modals, others) = List.partition (is_modal 1) l in
	  let stripped_modals = List.map strip_modal_op modals in
	    And( Modal(ModalOp(Diamond, 1), And( stripped_modals )) :: others )
	  else
	   f'
      )
    | _ -> f'

(*let rec opt_diamond_occur i form =
  opt_diamond_occur_rec i [] form*)
let rec opt_diamond_occur i form = 
  opt_diamond_occur_neg_rec i [] (opt_diamond_occur_pos_rec i [] form)
(*and opt_diamond_occur_rec i box_list_in form =
  let bl = (box_list_in @ (top_box i form) ) in
  let top_box_vars = List.fold_left IntSet.union IntSet.empty (List.map top_vars bl) in
    opt_diamond_occur_int i top_box_vars bl form*)
and opt_diamond_occur_pos_rec i box_list_in form =
  let bl = (box_list_in @ (top_box i form) ) in
  let top_neg_box_vars = List.fold_left IntSet.union IntSet.empty (List.map top_neg_vars bl) in
    opt_diamond_occur_pos_int i top_neg_box_vars bl form
and opt_diamond_occur_neg_rec i box_list_in form =
  let bl = (box_list_in @ (top_box i form) ) in
  let top_pos_box_vars = List.fold_left IntSet.union IntSet.empty (List.map top_pos_vars bl) in
    opt_diamond_occur_neg_int i top_pos_box_vars bl form
and top_box i form =
  match form with
      Modal(ModalOp(Box, i), f) -> [ f ]
    | And( l ) -> List.flatten (List.map (top_box i) l)
    | Or( l ) -> List.flatten (List.map (top_box i) l)
    | _ -> []
(*and opt_diamond_occur_int i box_vars bl form =
  match form with
      And( l ) -> And( List.map (opt_diamond_occur_int i box_vars bl) l )
    | Or( l ) -> Or( List.map (opt_diamond_occur_int i box_vars bl) l )
    | Modal(ModalOp(Diamond, i), f) -> Modal(ModalOp(Diamond, i), map_diamond_single_occur_rec i box_vars bl f)
    | _ -> form*)
and opt_diamond_occur_pos_int i neg_box_vars bl form =
  match form with
      And( l ) -> And( List.map (opt_diamond_occur_pos_int i neg_box_vars bl) l )
    | Or( l ) -> Or( List.map (opt_diamond_occur_pos_int i neg_box_vars bl) l )
    | Modal(ModalOp(Diamond, i), f) -> Modal(ModalOp(Diamond, i), map_diamond_single_occur_pos_rec i neg_box_vars bl f)
    | _ -> form
and opt_diamond_occur_neg_int i pos_box_vars bl form =
  match form with
      And( l ) -> And( List.map (opt_diamond_occur_neg_int i pos_box_vars bl) l )
    | Or( l ) -> Or( List.map (opt_diamond_occur_neg_int i pos_box_vars bl) l )
    | Modal(ModalOp(Diamond, i), f) -> Modal(ModalOp(Diamond, i), map_diamond_single_occur_neg_rec i pos_box_vars bl f)
    | _ -> form
(*and map_diamond_single_occur_rec i box_vars bl form =
  let opt_vars = IntSet.diff (top_single_vars form) box_vars in
  match form with
      Prop(i) -> if (IntSet.mem i opt_vars) then True else form
    | Not(Prop(i)) -> if (IntSet.mem i opt_vars) then True else form
    | And( l ) -> And( List.map (map_diamond_single_occur_rec i box_vars bl) l )
    | Or( l ) -> Or( List.map (map_diamond_single_occur_rec i box_vars bl) l )
    | Modal(m, f) -> let new_box_list = List.flatten ( List.map (top_box i) bl ) in
	Modal(m, opt_diamond_occur_rec i new_box_list f)
    | _ -> form*)
and map_diamond_single_occur_pos_rec i neg_box_vars bl form =
  let opt_vars = IntSet.diff (top_single_vars form) neg_box_vars in
  match form with
      Prop(i) -> if (IntSet.mem i opt_vars) then True else form
    | Not(Prop(i)) -> form
    | And( l ) -> And( List.map (map_diamond_single_occur_pos_rec i neg_box_vars bl) l )
    | Or( l ) -> Or( List.map (map_diamond_single_occur_pos_rec i neg_box_vars bl) l )
    | Modal(m, f) -> let new_box_list = List.flatten ( List.map (top_box i) bl ) in
	Modal(m, opt_diamond_occur_pos_rec i new_box_list f)
    | _ -> form
and map_diamond_single_occur_neg_rec i pos_box_vars bl form =
  let opt_vars = IntSet.diff (top_single_vars form) pos_box_vars in
  match form with
      Prop(i) -> form
    | Not(Prop(i)) -> if (IntSet.mem i opt_vars) then True else form
    | And( l ) -> And( List.map (map_diamond_single_occur_neg_rec i pos_box_vars bl) l )
    | Or( l ) -> Or( List.map (map_diamond_single_occur_neg_rec i pos_box_vars bl) l )
    | Modal(m, f) -> let new_box_list = List.flatten ( List.map (top_box i) bl ) in
	Modal(m, opt_diamond_occur_neg_rec i new_box_list f)
    | _ -> form
and top_pos_vars form = 
  match form with
      Prop(i) -> IntSet.singleton i
    | Not(Prop(i)) -> IntSet.empty
    | And( l ) -> List.fold_left IntSet.union IntSet.empty ( List.map pos_occur_prop l )
    | Or( l ) -> List.fold_left IntSet.union IntSet.empty ( List.map pos_occur_prop l )
    | Modal(m, f) -> IntSet.empty
    | _ -> IntSet.empty
and top_neg_vars form =
  match form with
      Prop(i) -> IntSet.empty
    | Not(Prop(i)) -> IntSet.singleton i
    | And( l ) -> List.fold_left IntSet.union IntSet.empty ( List.map pos_occur_prop l )
    | Or( l ) -> List.fold_left IntSet.union IntSet.empty ( List.map pos_occur_prop l )
    | Modal(m, f) -> IntSet.empty
    | _ -> IntSet.empty
and top_vars form =
  IntSet.union (top_pos_vars form) (top_neg_vars form)
and top_single_vars form =
  let pos = top_pos_vars form in
  let neg = top_neg_vars form in
  IntSet.diff (IntSet.union pos neg) (IntSet.inter pos neg)      

let opt_diamond form = 
  match form with
      And( l ) ->  (
	let unrolled = opt_unroll_diamond form in
	match (unrolled) with
	  Modal(ModalOp(Diamond, 1), f) -> f
	| _ -> unrolled
      )
    | _ -> form

let optimize f = 
  let g = nnf(opt_prop ( flatten ( bnf f))) in
  let h = opt_modal g in
  let p = opt_diamond h in
(*  let q = opt_diamond_occur 1 p in*)
  let r = opt_single_occur_prop p in
   r

let optimize_slow f = 
  let g = nnf (opt_prop ( flatten (bnf f))) in
  let h = opt_modal g in
  let p = opt_diamond h in
(*  let q = opt_diamond_occur 1 p in*)
  let r = opt_single_occur_prop p in
   r
(*
let optimize_slow f = 
  let g = opt_prop (flatten f) in
  let h = opt_modal g in
  let p = opt_single_occur_prop h in 
  let q = opt_diamond p in
  let r = opt_diamond_occur 1 q in
   q
*)

let optimize_rec f = 
  let g = opt_prop f in
  let h = opt_modal g in
  let p = opt_diamond h in
(*  let q = opt_diamond_occur 1 p in*)
  let r = opt_single_occur_prop p in
   r
(*
let optimize_rec f =
  let g = opt_prop f in
  let h = opt_modal g in
  let p = opt_single_occur_prop h in
  let q = opt_diamond p in
  let r = opt_diamond_occur 1 q in
   q
*)

let load_opt name =
  let f = load_k name in
  let i = propositions f in
  let m = map_new_prop_for_each_level 0 i f in
    optimize m

let rec opt_all_slow f = 
  let g = optimize_slow f in
    if (size g) = (size f) then
      g
    else
      opt_all_slow g

let rec opt_all f = 
  let g = optimize_rec f in
    if (size g) = (size f) then
      opt_all_slow g
    else
      opt_all g

let optimize_k f unmap =
  let i = propositions f in
  let m = map_new_prop_for_each_level 0 i f in
  let f'= optimize m in
  let g = opt_all f in
  let h = if (unmap = true) then
    unmap_prop_levels i g
  else
    g in
    h

