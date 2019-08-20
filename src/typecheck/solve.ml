open Typecheck_types
open Build_constraint
open Gensym
open Gen_t

let rec in_constraint_interior: g_node -> bound_target bound -> bool =
  fun g child -> begin match child.b_at with
      | `Ty t ->
          let t = Lazy.force t in
          let bound = (get_tyvar (UnionFind.get t)).ty_bound in
          in_constraint_interior g !bound
      | `G g' ->
          if g.g_id = g'.g_id then
            true
          else begin match g'.g_bound with
            | None -> false
            | Some {b_ty; b_at = next} ->
                in_constraint_interior g { b_ty; b_at = `G next }
          end
    end

let inst_bound: inst_edge -> g_node =
  fun {ie_ty_node; _} ->
  let rec go u =
    let bound = (get_tyvar (UnionFind.get u)).ty_bound in
    match !bound.b_at with
    | `Ty u' -> go (Lazy.force u')
    | `G g -> g
  in
  go ie_ty_node

let top_sort_inst
  : (g_node * (u_type UnionFind.var list)) IntMap.t
    -> (g_node * u_type UnionFind.var list) list
  = fun d ->
    let nodes = Map.keys d in

    let values = Map.to_alist d |> List.map ~f:snd in
    let edges =
      values
      |> List.map ~f:(fun (g, ts) ->
          List.map ts ~f:(fun t ->
              let g_to = inst_bound
                  { ie_g_node = g
                  ; ie_ty_node = t
                  }
              in
              Topological_sort.Edge.{
                from = g.g_id;
                to_ = g_to.g_id;
              }
            )
        )
      |> List.concat
    in
    begin match Topological_sort.sort (module Int) nodes edges with
      | Error _ ->
          MuleErr.bug "Topological sort failed"
      | Ok nodes_sorted ->
          List.filter_map nodes_sorted ~f:(Map.find d)
    end

(* Expand an instantiation constraint rooted at a g_node. See
 * section 3.1 of {MLF-Graph-Infer}.
*)
let expand: constraint_ops -> g_node -> g_node -> u_type UnionFind.var =
  fun cops old_g new_g ->
  let old_root = Lazy.force old_g.g_child in

  (* The logic in this function involves doing a deep copy of a graph
   * (not necessarily a tree). This map is used to handle shared
   * nodes; when we copy a node, we add a mapping from its old id to its
   * new one to the map. Before copying a node, we first check to see if
   * it's already in the map, and if so just return the existing copy.
  *)
  let visited = ref IntMap.empty in

  let rec go = fun kind nv new_root ->
    let n = UnionFind.get nv in
    let {ty_id = old_id; ty_bound} = get_tyvar n in
    let old_bound = !ty_bound in
    begin match Map.find !visited old_id with
      | Some new_node -> new_node
      | None ->
          if not (in_constraint_interior old_g old_bound) then
            begin
              (* We've hit the frontier; replace it with a bottom node and
               * constrain it to be equal to the old thing. *)
              let new_var = gen_u kind (`G new_g) in
              cops.constrain_unify nv new_var;
              new_var
            end
          else
            (* First, generate the new bound. *)
            let new_bound =
              ( if UnionFind.equal nv old_root then
                  { b_ty = `Flex
                  ; b_at = `G new_g
                  }
                else if Poly.equal old_bound.b_ty `Explicit then
                  begin match old_bound.b_at with
                    | `G _ -> MuleErr.bug "explicit binding points at g-node"
                    | `Ty at ->
                        let {ty_id = old_parent_id; _} =
                          Lazy.force at
                          |> UnionFind.get
                          |> get_tyvar
                        in
                        begin match Map.find !visited old_parent_id with
                          | None -> MuleErr.bug "node for parent not in map."
                          | Some new_parent_node ->
                              { b_ty = `Explicit
                              ; b_at = `Ty (lazy new_parent_node)
                              }
                        end
                  end
                else
                  { b_ty = old_bound.b_ty
                  ; b_at = `Ty new_root
                  }
              )
            in
            let new_tyvar =
              { ty_id = gensym ()
              ; ty_bound = ref new_bound
              }
            in

            (* Add a fresh unification variable to the map up front, in case we
             * hit a recursive type. We'll merge it with the final result below. *)
            let map_copy = UnionFind.make (`Free (new_tyvar, kind)) in
            visited := Map.set !visited ~key:old_id ~data:map_copy;

            (* Now do a deep copy, subbing in the new bound. *)
            let ret = UnionFind.make (match n with
                | `Free _ -> `Free (new_tyvar, kind)
                | `Quant (_, arg) ->
                    `Quant(new_tyvar, go kind arg new_root)
                | `Const(_, c, args, _) ->
                    `Const
                      ( new_tyvar
                      , c
                      , List.map args ~f:(fun (t, k) -> (go k t new_root, k))
                      , kind
                      ))
            in

            (* ...and do the merge. Rather than call unify, we just overwrite with
             * the final value; there's no real unification going on here, we just
             * need to avoid cycles. *)
            UnionFind.merge
              (fun _ r -> r)
              map_copy
              ret;
            ret
    end
  in
  let rec new_root = lazy (go kvar_type old_root new_root) in
  Lazy.force new_root

let propagate: constraint_ops -> g_node -> u_type UnionFind.var -> unit =
  fun cops g var ->
  begin match (get_u_bound (UnionFind.get var)).b_at with
    | `G g' ->
        let instance = expand cops g g' in
        cops.constrain_unify instance var
    | `Ty _ ->
        MuleErr.bug "propagate: node not bound at g-node."
  end

let solve_constraints cs =
  let render_ucs = ref cs.unification in
  let render_ics = ref cs.instantiation in
  let render_kcs = ref cs.kind in
  Debug.render_hook := (fun () -> Render.render_graph
                           { unification = !render_ucs
                           ; instantiation = !render_ics
                           ; kind = !render_kcs
                           ; ty = cs.ty
                           }
                       );
  List.iter cs.kind ~f:(fun (x, y) -> UnionFind.merge Infer_kind.unify x y);
  let solve_unify vars =
    render_ucs := vars;
    List.iter vars ~f:(fun (Unify (l, r)) ->
        !Debug.render_hook ();
        Unify.normalize_unify l r;
        render_ucs := List.tl_exn !render_ucs;
      );
    !Debug.render_hook ()
  in
  solve_unify cs.unification;
  top_sort_inst cs.instantiation
  |> List.iter ~f:(fun (g, ts) ->
      List.iter ts ~f:(fun t ->
          let cops, ucs, _, _kcs = make_cops () in
          propagate cops g t;
          render_ucs := !ucs;
          !Debug.render_hook ();
          render_ics := Map.update !render_ics g.g_id ~f:(function
              | None -> MuleErr.bug "impossible"
              | Some (g, xs) -> (g, List.tl_exn xs)
            );
          solve_unify !ucs;
        );
      render_ics := Map.remove !render_ics g.g_id
    );
  !Debug.render_hook ();
  cs.ty

