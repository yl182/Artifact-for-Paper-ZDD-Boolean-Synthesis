type modaloptype = Box | Diamond
type modalop = ModalOp of modaloptype * int
type formula = True | False | Prop of int | And of (formula list) | Or of (formula list) | Not of formula | Modal of modalop * formula | Invalid

let is_diamond f = 
  match f with
      Modal(ModalOp(Diamond, _), _) -> true
    | _ -> false

let is_box f = 
  match f with
      Modal(ModalOp(Box, _), _) -> true
    | _ -> false

let is_modal f = 
  match f with
      Modal(_, _) -> true
    | _ -> false

let is_not f = 
  match f with
      Not(_) -> true
    | _ -> false

let strip f =
  match f with
      Modal(_, f) -> f
    | _ -> Invalid

let strip_not f =
  match f with
      Not(f) -> f
    | _ -> Invalid

let is_lean f =
  match f with
      Prop(_) | Modal(_,_) | Not(_) -> true
    | _ -> false

module Formula =
  struct
    type t = formula
    let compare = Pervasives.compare
  end
module FormulaSet = Set.Make(Formula)

let to_set l =
  List.fold_right FormulaSet.add l FormulaSet.empty
