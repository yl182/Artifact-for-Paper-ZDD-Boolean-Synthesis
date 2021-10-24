module type OrderedType = sig
  type t
  val compare: t -> t -> int
end

class type ['elt] contextclass = 
object
  method update_move: int -> int -> 'elt -> unit
  method update_insert: int -> 'elt -> unit
  method update_delete: int -> 'elt -> unit
end
	  
class type ['t] heap = 
object
  method is_empty : bool
  method add: 't -> unit
  method max_elt: 't
  method pop: unit
  method update: int -> 't -> unit
  method to_list: 't list
  method elements: 't list
  method get: int -> 't
  method clear: unit
end

module GenericBinaryHeap =
  functor (T:OrderedType) -> struct
    exception Not_found
    class ['containert] heapimplementation ct = 
    object (self : T.t #heap)
      constraint 'containert = T.t #contextclass
      val mutable size:int = 0
      val mutable data:T.t array = [||]
      val mutable context:T.t #contextclass ref = ref ct
      method private grow elem = 
	let s = Array.length data in
	let new_size = if (s=0) then 16 else s * 2 in
	let d = Array.make new_size elem in
	  Array.blit data 0 d 0 size;
	  data <- d
      method private maintain_heap_up i e =
	let j = ref i in
	  while !j >= 1 && (T.compare data.(!j/2) e)<0 do
	    data.(!j) <- data.(!j/2);
	    !context#update_move (!j/2) (!j) data.(!j);
	    j := !j/2
	  done;
	  !j
      method private maintain_heap_down i e =
	let max_index = size-1 in
	let j = ref i in
	let k = ref (!j*2+1) in
	  while !k<=max_index do
	    k := if !k<max_index && (T.compare data.(!k+1) data.(!k)>0) then (!k+1) else (!k);
	    if T.compare data.(!k) e > 0 then (
	      data.(!j) <- data.(!k);
	      !context#update_move !k !j data.(!j);
	      j := !k;
	      k := !j*2+1
	    ) else
	      k := max_index+1
	  done;
	  !j
      method is_empty = (size = 0)
      method get i = data.(i)
      method max_elt = if size=0 then raise Not_found else data.(0)
      method add e = 
	if size+1>(Array.length data) then
	  self#grow e
	else ();
	let n = size in
	let j = self#maintain_heap_up n e in
	  data.(j) <- e;
	  !context#update_insert j data.(j);
	  size <- size+1
      method update i e =
	let j = self#maintain_heap_up i e in
	  data.(j) <- e;
	  !context#update_move i j e
      method pop = 
	if size<=0 then raise Not_found else ();
	let max_index = size-1 in
	let max = data.(0) in
	let e = data.(max_index) in
	let j = self#maintain_heap_down 0 e in
	  data.(j) <- e;
	  !context#update_move max_index j data.(j);
	  !context#update_delete 0 max;
	  size <- size-1;
      method to_list =
	if self#is_empty then [] else 
	  let x = self#max_elt in
	    self#pop;
	    x::(self#to_list)  
      method elements = 
	Array.to_list (Array.sub data 0 size)
      method clear = 
	while not self#is_empty do
	  self#pop
	done
    end
    type t = T.t contextclass heapimplementation
  end

class ['elt] nullcontext =
object (self : 'elt #contextclass)
  method update_move orig dest e = ()
  method update_insert dest e = ()
  method update_delete src e = ()
end

module Heap = 
  functor (T:OrderedType) -> struct
    module Implementation = GenericBinaryHeap(T)
    type contexttype = T.t contextclass
    class heap = object
      inherit [contexttype] Implementation.heapimplementation (new nullcontext)
    end
    type t = heap
  end
