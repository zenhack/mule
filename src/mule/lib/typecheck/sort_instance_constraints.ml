module GT = Graph_types
module C = Constraint_t

let rec g_for_q : Context.t -> GT.quant GT.var -> GT.g_node =
  fun ctx qv ->
    let q = Context.read_var ctx Context.quant qv in
    let b = Context.read_var ctx Context.bound q.GT.q_bound in
    match b.GT.b_target with
      | `G g -> g
      | `Q qv' -> g_for_q ctx qv'

let constraint_edge : Context.t -> C.instance_constraint -> GT.Ids.G.t Tsort.edge =
  fun ctx C.{inst_super = g; inst_sub = q; _} ->
    let qg = g_for_q ctx q in
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
    let nodes = List.map cs ~f:(fun c -> GT.GNode.id c.C.inst_super) in
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
