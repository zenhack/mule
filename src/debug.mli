include module type of Debug_t

val start_graph: unit -> unit
val show_node: node_type -> int -> unit
val show_edge: edge_type -> int -> int -> unit
val end_graph: unit -> unit
val set_root: int -> unit
