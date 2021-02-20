module GT = Graph_types
module C = Constraint_t

module Util = Typecheck_util

let constraint_edge : Context.t -> C.instance_constraint -> GT.Ids.G.t Tsort.edge =
  fun ctx C.{inst_super = g; inst_sub = q; _} ->
    let qg = Util.g_for_q ctx q in
    Tsort.{
      from = GT.GNode.id g;
      to_ = GT.GNode.id qg;
    }

let must_not_cycle = function
  | `Single v -> v
  | `Cycle _ -> MuleErr.bug "Cycle in instance constraints"

let g_node_order : Context.t -> C.instance_constraint list -> GT.Ids.G.t list =
  fun ctx cs ->
    let edges = List.map cs ~f:(constraint_edge ctx) in
    let nodes = List.concat_map cs ~f:(fun c ->
        [
          GT.GNode.id c.C.inst_super;
          GT.GNode.id (Util.g_for_q ctx c.C.inst_sub);
        ]
      )
    in
    Tsort.sort
      (module GT.Ids.G)
      ~edges
      ~nodes
    |> List.map ~f:must_not_cycle

module GNodeMap = MapSet.MkMap(GT.Ids.G)

let constraints_by_g : C.instance_constraint list -> C.instance_constraint list GNodeMap.t =
  List.fold
    ~init:(Map.empty (module GT.Ids.G))
    ~f:(fun map c ->
      Map.update map (GT.GNode.id c.C.inst_super) ~f:(function
        | None -> [c]
        | Some cs -> c :: cs
      )
    )

let sort ctx input_cs =
  let node_order = g_node_order ctx input_cs in
  let map = constraints_by_g input_cs in
  List.concat_map node_order ~f:(fun id ->
    match Map.find map id with
    | None -> []
    | Some cs -> cs
  )
