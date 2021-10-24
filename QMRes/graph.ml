open Common
open Heap

module type OrderedType = sig
  type t
  val compare: t -> t -> int
end

module VS = IntSet

module type GraphType = sig
  type t
  val empty: t
  val is_empty: t -> bool
  val resize: t -> int -> t
  val connect: t -> int -> int -> unit
  val is_connected: t -> int -> int -> bool
  val degree_out: t -> int -> int
  val degree_in: t -> int -> int
  val succ: t -> int -> VS.t
  val pred: t -> int -> VS.t
  val iter: (t -> int -> unit) -> t -> unit
  val print: t -> unit
end 

module type TaggedGraphType = 
  functor (Tag:OrderedType) -> sig
    include GraphType
    val assoc_vertex: t -> int -> Tag.t -> unit
    val find_vertex: t -> Tag.t -> int
    val find_tag: t -> int -> Tag.t
    val connect_by_tag: t -> Tag.t -> Tag.t -> unit
  end 

module BaseDirectedGraph = struct
  type t = { vertices:int; mutable forEdges: VS.t array; mutable backEdges: VS.t array }
  type graphtype = t
  let empty = { vertices = 0; forEdges = [||]; backEdges = [||] }
  let is_empty g = g.vertices <= 0
  let resize g size = 
    let forEdges' = Array.create size VS.empty in
    let backEdges' = Array.create size VS.empty in
      Array.blit g.forEdges 0 forEdges' 0 (min g.vertices size);
      Array.blit g.backEdges 0 backEdges' 0 (min g.vertices size);
      { vertices=size; forEdges=forEdges'; backEdges=backEdges' }
  let connect g ida idb =
    g.forEdges.(ida) <- VS.add idb g.forEdges.(ida);
    g.backEdges.(idb) <- VS.add ida g.backEdges.(idb)
  let is_connected g ida idb = VS.mem idb g.forEdges.(ida)
  let degree_out g id = VS.cardinal g.forEdges.(id)
  let degree_in g id = VS.cardinal g.backEdges.(id)
  let succ g id = g.forEdges.(id)
  let pred g id = g.backEdges.(id)
  let iter f g = 
    for i = 0 to g.vertices - 1 do
      f g i
    done
  let print g = ()
end
  
module BaseUndirectedGraph = struct 
  type t = { vertices:int; mutable forEdges: VS.t array}
  type graphtype = t
  let empty = { vertices = 0; forEdges = [||] }
  let is_empty g = g.vertices <= 0
  let resize g size = 
    let forEdges' = Array.make size VS.empty in
      Array.blit g.forEdges 0 forEdges' 0 (min g.vertices size);
      { vertices=size; forEdges=forEdges' }
  let connect g ida idb =
    g.forEdges.(ida) <- VS.add idb g.forEdges.(ida);
    g.forEdges.(idb) <- VS.add ida g.forEdges.(idb)
  let is_connected g ida idb =
    IntSet.mem idb g.forEdges.(ida)
  let degree_out g id = VS.cardinal g.forEdges.(id)
  let degree_in = degree_out
  let succ g id = g.forEdges.(id)
  let pred = succ
  let iter f g =
    for i = 0 to g.vertices - 1 do
      f g i
    done
  let print g =
    Printf.printf "Graph of %d nodes\n" g.vertices;
      for i = 0 to g.vertices-1 do
	Printf.printf "Neighbor of %d: " i;
	print_int_list (IntSet.elements (succ g i));
	print_string "\n"
      done;
      ()
end

module VertexTaggedGraph(G:GraphType)(TagType:OrderedType) = struct
    module VertexToTagMap = IntMap
    module TagToVertexMap = Map.Make(TagType)
    type t = { mutable g:G.t; mutable tagMap:TagType.t VertexToTagMap.t; mutable vertexMap:int TagToVertexMap.t }
    type vertextaggedgraphtype = t
    let empty = { g = G.empty; tagMap = VertexToTagMap.empty; vertexMap = TagToVertexMap.empty }
    let is_empty g = G.is_empty g.g
    let resize g size = g.g <- G.resize g.g size
    let connect g ida idb = G.connect g.g ida idb 
    let is_connected g ida idb = G.is_connected g.g ida idb
    let assoc_vertex g id tag =
      g.tagMap <- VertexToTagMap.add id tag g.tagMap;
      g.vertexMap <- TagToVertexMap.add tag id g.vertexMap
    let find_vertex g tag =
      TagToVertexMap.find tag g.vertexMap
    let find_tag g id =
      VertexToTagMap.find id g.tagMap
    let connect_by_tag g taga tagb =
      let ida = find_vertex g taga in
      let idb = find_vertex g tagb in
	connect g ida idb
    let degree_out g id = G.degree_out g.g id
    let degree_in g id = G.degree_in g.g id
    let succ g id = G.succ g.g id
    let pred g id = G.pred g.g id
    let iter f g = G.iter f g.g
    let print g = G.print g.g
  end
  
module type VertexOrder = sig
  module Graph:GraphType
  type t
  val init: Graph.t -> t
  val sort: t -> int list
  val shutdown: t -> unit
end

module VertexOrderMinDegree = 
  functor (G:GraphType) -> struct
    module Graph = G
    module TaggedPair = struct
      type t = int * int
      let compare (a1,a2) (b1,b2) = -(Pervasives.compare a2 b2)
    end
    module MinDegreeHeap = Heap(TaggedPair)
    type t = MinDegreeHeap.t
    let init g =
      let h = new MinDegreeHeap.heap in
	Graph.iter (fun g i -> h#add (i,(Graph.degree_in g i))) g;
	h
    let sort h = 
      let l = h#to_list in
      let (l',_) = List.split l in
	l'
    let shutdown h = ()
  end

module VertexOrderMaxCardinality = 
  functor (G:GraphType) -> struct
    module Graph = G
    module MaxCardinalityElement = struct
      type t = { var:int; ncount:int; degree:int}
      let compare a b = 
	let x = Pervasives.compare a.ncount b.ncount in
	  if x = 0  then 
	    if !(Options.min_degree_on_card) then
	      Pervasives.compare (-a.degree) (-b.degree)
	    else
	      Pervasives.compare a.degree b.degree 
	    else x
      let var x = x.var
      let succ x = { var=x.var; ncount=x.ncount+1; degree=x.degree }
      let make a b c = { var=a; ncount=b; degree=c }
      let print x = Printf.printf " var=%d, ncount = %d; degree=%d " x.var x.ncount x.degree
    end
    module T = MaxCardinalityElement
    class maxcardinalitycontext g' = 
    object (self: T.t #contextclass) 
      val g:Graph.t ref = ref g'
      val mutable h:T.t heap ref option = None
      val mutable m:int IntMap.t = IntMap.empty
      method set_heap h' = h <- Some(ref h')
      method update_move src dest elem = 
(*	Printf.printf " %d moved from %d to %d\n" (T.var elem) src dest;*)
	m <- IntMap.add (T.var elem) dest m
      method update_insert dest elem =
(*	Printf.printf " %d inserted at %d \n" (T.var elem) dest;*)
	m <- IntMap.add (T.var elem) dest m
      method update_delete src elem = 
(*	Printf.printf " %d deleted at %d \n" (T.var elem) src;*)
	let Some(hh) = h in
	let neighbors = Graph.succ !g (T.var elem) in
	  m <- IntMap.remove (T.var elem) m;
	  VS.iter (fun i ->
		     if (IntMap.mem i m) then (
(*		       Printf.printf "looking for %d" i;*)
		       let offset = IntMap.find i m in
(*			 Printf.printf " found at %d " offset;*)
		       let e = !hh#get offset in
(*			 Printf.printf " var is %d\n" (T.var e);*)
		       let e' = T.succ e in
			 !hh#update offset e'
		     ) else ()
		  ) neighbors
    end
    module MaxCardinalityHeap = GenericBinaryHeap(MaxCardinalityElement)
    type t = MaxCardinalityHeap.t
    let init g = 
      if !Options.debug_graph > 0 then
	Graph.print g;
      let context = new maxcardinalitycontext g in
      let h = new MaxCardinalityHeap.heapimplementation context in
	context#set_heap h;
	Graph.iter (fun g i -> (*if (Graph.degree_out g i) > 0 then*)
		      h#add (T.make i 0 (Graph.degree_out g i)) ) g;
	h
    let sort h = 
      let l = h#to_list in 
      let l' = List.map T.var l in
	List.rev l'
    let shutdown g = ()
  end

module VertexOrderLayeredMaxCardinality =
  functor (G:GraphType) -> struct
    module Graph=G
    module IMP = VertexOrderMaxCardinality(G)
    module MaxCardinalityElement = IMP.MaxCardinalityElement
    module T = MaxCardinalityElement
    class maxcardinalitycontext g' = IMP.maxcardinalitycontext g'
    module MaxCardinalityHeap = GenericBinaryHeap(MaxCardinalityElement)
    type t = MaxCardinalityHeap.t
    let rec sort_ g vll sl ss = 
      let sort_int g vl vs = 
	let context = new maxcardinalitycontext g in
	let h = new MaxCardinalityHeap.heapimplementation context in
	  context#set_heap h;
	  let _ = List.map (fun v -> if (Graph.degree_out g (v-1)) > 0 then
			      h#add (T.make (v-1) (VS.cardinal (VS.inter vs (Graph.succ g (v-1)))) (Graph.degree_out g (v-1))); () ) vl in 
	  let l = h#to_list in
	  let l' = List.map MaxCardinalityElement.var l in
	  let vs' = List.fold_right VS.add l' vs in
	    (l', vs')
      in
	match vll with
	    [] -> (sl, ss)
	  | hd::tl -> let (sl', ss') = sort_int g hd ss in
	      sort_ g tl (sl@[sl']) ss'
    let sort g vll =
      let (sl, _) = sort_ g vll [] VS.empty in
	List.flatten sl
  end

