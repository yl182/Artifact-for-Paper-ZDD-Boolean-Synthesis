
module Graph = struct
  type graph
  external init: int -> graph = "init_graph_rgl"
  external add_edge: graph -> int -> int -> unit = "add_edge_graph_rgl"
  external lex_bfs: graph -> int list = "lex_bfs_rgl"
  external lex_bfs_min: graph -> int list = "lex_bfs_min_rgl"
  external mcs: graph -> int list = "mcs_rgl"
  external mcs_layered: graph -> int list = "mcs_rgl_layered"
  external min_induced_width: graph -> int list = "min_induced_width_rgl"
  external min_fill: graph -> int list = "min_fill_rgl"
  external new_alg: graph -> int list = "new_alg_rgl"
  external width: graph -> int list -> int = "tree_width_rgl"
  external triangulate : graph -> int list -> int = "triangulate_graph_rgl"
  external build_tree_decomposition: graph -> int list -> graph = "build_tree_decomposition_rgl"
  external reroot_tree_decomposition: graph -> int list -> int list = "reroot_tree_decomposition_rgl"
  external set_order_sign: int -> unit = "set_order_sign_rgl"
  external set_order_tiebreaker: int -> unit = "set_order_tiebreaker_rgl"
  external set_secondary_tiebreaker: int -> unit = "set_secondary_tiebreaker_rgl"
  external set_width_min_degree_heuristic: unit -> unit = "set_width_min_degree_rgl"
  external associate_vertex: graph -> int -> int -> unit = "associate_graph"
  external sift_graph_width: graph -> int -> int list -> int list = "sift_graph_width_rgl"
end

