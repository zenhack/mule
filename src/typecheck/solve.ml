open Typecheck_types
open Build_constraint
open Gensym
open Gen_t
open Unify

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
          failwith "Topological sort failed"
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
     * (not necessarily a tree). These two maps are used to handle shared
     * nodes; when we copy a node, we add a mapping from its old id to its
     * new one to the appropriate map. Before copying a node, we first
     * check to see if it's already in the map, and if so just return the
     * existing copy. *)
    let visited_types = ref IntMap.empty in
    let visited_rows = ref IntMap.empty in

    (* XXX: go and go_row have too much redundancy *)
    let rec go = fun nv new_root ->
      let n = UnionFind.get nv in
      let {ty_id = old_id; ty_bound} = get_tyvar n in
      let old_bound = !ty_bound in
      begin match Map.find !visited_types old_id with
        | Some new_node -> Lazy.force new_node
        | None ->
            if not (in_constraint_interior old_g old_bound) then
              begin
                (* We've hit the frontier; replace it with a bottom node and
                 * constrain it to be equal to the old thing. *)
                let new_var = gen_u (`G new_g) in
                cops.constrain_ty nv new_var;
                new_var
              end
            else
              (* First, generate the new bound. *)
              let new_bound =
                  ( if UnionFind.equal nv old_root then
                      { b_ty = `Flex
                      ; b_at = `G new_g
                      }
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
              (* Add a copy to the map up front, in case we hit a recursive type.
               * We'll have to unify it with the final result below. *)
              visited_types := Map.set !visited_types ~key:old_id ~data:(lazy(
                (* Now do a deep copy, subbing in the new bound. *)
                UnionFind.make (match n with
                  | `Free _ -> `Free new_tyvar
                  | `Fn (_, param, ret) -> `Fn(new_tyvar, go param new_root, go ret new_root)
                  | `Record(_, row) -> `Record(new_tyvar, go_row row new_root)
                  | `Union(_, row) -> `Union(new_tyvar, go_row row new_root))
              ));
              Lazy.force (Map.find_exn !visited_types old_id)
      end

    and go_row row_var new_root =
      let row = UnionFind.get row_var in
      let {ty_id = old_id; ty_bound} = get_tyvar row in
      let old_bound = !ty_bound in
      begin match Map.find !visited_rows old_id with
        | Some new_node -> Lazy.force new_node
        | None ->
          if not (in_constraint_interior old_g old_bound) then
            begin
              (* On the frontier. *)
              let new_var = gen_u (`G new_g) in
              cops.constrain_row row_var new_var;
              new_var
            end
          else begin
            let new_tv =
              { ty_id = gensym ()
              ; ty_bound = ref
                { b_ty = old_bound.b_ty
                ; b_at = `Ty new_root
                }
              }
            in
            visited_rows := Map.set !visited_rows ~key:old_id ~data:(lazy(
              UnionFind.make (match row with
                | `Extend(_, l, ty, rest) -> `Extend(new_tv, l, go ty new_root, go_row rest new_root)
                | `Empty _ -> `Empty new_tv
                | `Free _ -> `Free new_tv)
            ));
            Lazy.force (Map.find_exn !visited_rows old_id)
          end
      end
    in
    let rec new_root = lazy (go old_root new_root) in
    Lazy.force new_root

let propagate: constraint_ops -> g_node -> u_type UnionFind.var -> unit =
  fun cops g var ->
    begin match (get_u_bound (UnionFind.get var)).b_at with
      | `G g' ->
        let instance = expand cops g g' in
        cops.constrain_ty instance var
      | `Ty _ ->
          failwith "propagate: node not bound at g-node."
    end

let solve_constraints cs =
  let render_ucs = ref cs.unification in
  let render_ics = ref cs.instantiation in
  let render () = Render.render_graph
    { unification = !render_ucs
    ; instantiation = !render_ics
    ; ty = cs.ty
    }
  in
  let solve_unify vars =
    render_ucs := vars;
    List.iter vars ~f:(fun c ->
      render ();
      begin match c with
      | UnifyTypes(l, r) -> UnionFind.merge unify l r
      | UnifyRows(l, r) -> UnionFind.merge unify_row l r
      end;
      render_ucs := List.tl_exn !render_ucs;
    );
    render ()
  in
  solve_unify cs.unification;
  top_sort_inst cs.instantiation
  |> List.iter ~f:(fun (g, ts) ->
      List.iter ts ~f:(fun t ->
        let cops, ucs, _ = make_cops () in
        propagate cops g t;
        render_ucs := !ucs;
        render ();
        render_ics := Map.update !render_ics g.g_id ~f:(function
          | None -> failwith "impossible"
          | Some (g, xs) -> (g, List.tl_exn xs)
        );
        solve_unify !ucs;
      );
      render_ics := Map.remove !render_ics g.g_id
    );
  cs.ty

