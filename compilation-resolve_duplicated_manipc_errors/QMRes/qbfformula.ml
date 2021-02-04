open Common

exception Bad_formula

type quantifiertype = [`Forall | `Exists]
type quantifier = quantifiertype * (int list)
type formula = [`True | `False | `Prop of int | `And of (formula list) | `Or of (formula list) | `Not of formula | `Quant of quantifier * formula | `Invalid]

let rec props f =
  match f with
      `True | `False | `Invalid -> 0
    | `Prop(i) -> i
    | `Not(g) -> props g
    | `Quant((_,q), g) -> let p1 = props g in
      let p2 = List.fold_left max 0 q in
      let p = max p1 p2 in
	p
    | `And(l) | `Or(l) -> let pl = List.map props l in
	List.fold_left max 0 pl
    | _ -> 0

let rec support_vars f =
  match f with
      `True | `False | `Invalid -> IntSet.empty
    | `Prop(i) -> IntSet.singleton i
    | `Not(g) -> support_vars g
    | `Quant((_,q), g) -> IntSet.union (support_vars g) (List.fold_right IntSet.add q IntSet.empty)
    | `And(l) | `Or(l) -> List.fold_right (fun f s -> IntSet.union (support_vars f) s) l IntSet.empty
    | _ -> IntSet.empty

let rec unroll_quant f q =
  match q with 
      [] -> f
    | hd::tl -> `Quant(hd, unroll_quant f tl)

let build_prop_quants f =
  let rec build_quant_int f =
    let vars = 
      match f with
	  `And(l) | `Or(l) -> List.fold_left (fun x y -> IntSet.union x (build_quant_int y)) IntSet.empty l
	| `Prop(v) -> IntSet.singleton v
	| `Not(`Prop(v)) -> IntSet.singleton v
	| _ -> IntSet.empty
    in
      vars
  in
  let v = build_quant_int f in
    `Quant((`Exists, IntSet.elements v), f)

let rec support f = 
  match f with
      `True | `False | `Invalid -> IntSet.empty
    | `Prop(i) -> IntSet.singleton i
    | `Not(g) -> support g
    | `And(l) | `Or(l) -> let l' = List.map support l in
	List.fold_left IntSet.union IntSet.empty l'
    | `Quant(q,g) -> support g
	
let rec map_vars vo f =
  match f with 
      `Prop(i) -> `Prop(vo.(i))
    | `Not(g) -> `Not(map_vars vo g)
    | `And(l) -> `And(List.map (map_vars vo) l)
    | `Or(l) -> `Or(List.map (map_vars vo) l)
    | `Quant(q,g) ->
	let (qu, qv) = q in
	let qv' = List.map (fun y -> vo.(y)) qv in
	  `Quant((qu,qv'), map_vars vo g)
    | _ -> f

