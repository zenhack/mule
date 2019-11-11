include Tsort_t

(* Most of the things declared in this module are helpers for [sort],
 * defined at the bottom of the file.
 *)

(* A set of nodes which are (possibly) part of a cycle.
 *
 * If ns_nodes is a singleton set, there may not actually be a cycle.
 *)
type ('n, 'cmp) node_set = {
  ns_nodes: ('n, 'cmp) Set.t; (* The actual set. *)
  ns_repr: 'n; (* A distinguished "representative" of the set. *)
  ns_to: ('n, 'cmp) Set.t; (* The set of outgoing edges from these nodes. *)
}

(* Make an initial map mapping each node to a singleton [node_set UnionFind.var]
 * containing only itself, with no edges. *)
let make_init_map comparator ~nodes =
  List.fold
    nodes
    ~init:(Map.empty comparator)
    ~f:(fun old n ->
      Map.set old ~key:n ~data:(UnionFind.make {
          ns_nodes = Set.singleton comparator n;
          ns_repr = n;
          ns_to = Set.empty comparator;
        })
    )

(* Add the list of edges to the map.
 *
 * - [map] is a map from nodes to [node_set UnionFind.var]s, where the keys are
 *   members of their corresponding sets.
 * - [edges] is a list of edges.
 *
 * add_edges will populate the [ns_to] field of the values with
 * each edge that it finds.
 *)
let add_edges map ~edges =
  List.iter edges ~f:(fun {to_; from} ->
    let fsv = Util.find_exn map from in
    let fs = UnionFind.get fsv in
    UnionFind.set
      { fs with ns_to = Set.add fs.ns_to to_ }
      fsv
  )

(* Join sets in [map] that have cycles.
 *
 * [map] is a map from nodes to [node_set UnionFind.var]s.
 *
 * [join_cycles] merges values that are part of a cycle in the
 * graph, based on the [ns_to] fields
 *)
let join_cycles comparator map =
  let rec go ~parents node =
    let nsv = Util.find_exn map node in
    let ns = UnionFind.get nsv in
    if Set.mem parents node then
      ignore (Set.fold
        parents
        ~init:nsv
        ~f:(fun lsv r -> UnionFind.merge (fun l r -> {
              ns_nodes = Set.union l.ns_nodes r.ns_nodes;
              ns_repr = l.ns_repr;
              ns_to = Set.union l.ns_to r.ns_to;
            })
            lsv
            (Util.find_exn map r);
            lsv
        ))
    else
      Set.iter ns.ns_to ~f:(fun to_ ->
        go
          ~parents:(Set.add parents node)
          to_
      )
  in
  let empty_set = Set.empty comparator in
  Map.iter_keys map ~f:(go ~parents:empty_set)

(* Remove all items from [map] whose keys are not the representative for
 * their set, and change all references in [ns_to] fields to refer to
 * representatives.
 *
 * [map] is a map from nodes to [node_set UnionFind.var]s, the return
 * value is a map from nodes to [node_set]s.
 * *)
let prune_non_reprs comparator map =
  let reprs =
    Map.fold
      map
      ~init:(Set.empty comparator)
      ~f:(fun ~key:_ ~data old ->
        Set.add old (UnionFind.get data).ns_repr
      )
  in
  Map.filter_mapi map ~f:(fun ~key ~data ->
    let ns = UnionFind.get data in
    if Set.mem reprs key then
      let ns_to = Set.map comparator ns.ns_to ~f:(fun n ->
          Util.find_exn map n
          |> UnionFind.get
          |> fun {ns_repr; _} -> ns_repr
        )
      in
      Some { ns with ns_to }
    else
      None
  )

(* Do a depth-first traversal of the graph, and call f on each set of
 * nodes.
 *
 * [map] should be a map as returned by [prune_non_reprs].
 *)
let iter_depth_first comparator map ~f =
  let seen = ref (Set.empty comparator) in
  let rec go {ns_nodes; ns_repr; ns_to} =
    if Set.mem !seen ns_repr then
      ()
    else
      begin
        seen := Set.add !seen ns_repr;
        Set.iter ns_to ~f:(fun n ->
          go (Util.find_exn map n)
        );
        f ns_nodes
      end
  in
  Map.iter map ~f:go

let sort (type n) (module Node : Comparator.S with type t = n) ~nodes ~edges =
  let map = make_init_map (module Node) ~nodes in
  add_edges map ~edges;
  join_cycles (module Node) map;
  let map = prune_non_reprs (module Node) map in
  let ret = ref [] in
  iter_depth_first (module Node) map ~f:(fun ns ->
    ret := (Set.to_list ns) :: !ret
  );
  List.rev !ret
