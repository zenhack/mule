
val report: bool -> (unit -> string) -> unit

type edge_type =
  [ `Structural of string
  | `Unify
  | `Instance
  | `Binding of [ `Flex | `Rigid ]
  ]
type node_type =
  [ `TyVar
  | `TyFn
  | `TyRecord
  | `TyUnion
  | `RowVar
  | `RowEmpty
  | `RowExtend of Ast.Label.t
  | `G
  ]

val start_graph: unit -> unit
val show_node: node_type -> int -> unit
val show_edge: edge_type -> int -> int -> unit
val end_graph: unit -> unit
val set_root: int -> unit
