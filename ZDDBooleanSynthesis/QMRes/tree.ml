open Common

type tree = { mutable size:int; mutable parent: int IntMap.t; mutable children: IntSet.t IntMap.t }

let empty () = { size = 1; parent = IntMap.empty; children = IntMap.empty }

let add p t = 
  let index = t.size in
    t.size <- t.size+1;
    t.parent <- IntMap.add index p t.parent;
    let _ =
      if IntMap.mem p t.children then
	let s = IntMap.find p t.children in
	  t.children <- IntMap.add p (IntSet.add index s) t.children
      else
	t.children <- IntMap.add p (IntSet.singleton index) t.children
    in
      index

let is_root n t =
  if n=0 then true else false

let parent n t =
  if n=0 then raise Not_found
  else
    IntMap.find n t.parent

let children n t =
  if IntMap.mem n t.children then
    IntMap.find n t.children
  else
    IntSet.empty

let siblings n t =
  children (parent n t) t
