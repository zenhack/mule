open Typecheck_types
open Build_constraint

(* TODO: why are we using a map to unit here, rather than a set? *)
let rec emit_all_nodes_ty: u_type UnionFind.var -> unit IntMap.t ref -> unit =
  fun v dict ->
  let t = UnionFind.get v in
  let {ty_id = n; ty_bound} = get_tyvar t in
  if Map.mem !dict n then
    ()
  else begin
    dict := Map.set !dict ~key:n ~data:();
    emit_bind_edge n !ty_bound dict;
    begin match t with
      | `Free _ ->
          Debug.show_node `TyVar n
      | `Quant (_, arg) ->
          Debug.show_node (`Const (`Named "Q")) n;
          let v_id = (get_tyvar (UnionFind.get arg)).ty_id in
          Debug.show_edge `Structural n v_id;
          emit_all_nodes_ty arg dict
      | `Const(_, c, args, _) ->
          Debug.show_node (`Const c) n;
          let n_ids = List.map args
              ~f:(fun (uvar, _) ->
                  let v_id = (get_tyvar (UnionFind.get uvar)).ty_id in
                  Debug.show_edge `Structural n v_id;
                  emit_all_nodes_ty uvar dict;
                  v_id
                )
          in
          begin match n_ids with
            | [] -> ()
            | (i :: is) ->
                ignore (List.fold_left
                          is
                          ~init:i
                          ~f:(fun l r ->
                              Debug.show_edge `Sibling l r;
                              r
                            ))
          end
    end
  end
and emit_all_nodes_g g dict =
  if Map.mem !dict g.g_id then
    ()
  else begin
    dict := Map.set !dict ~key:g.g_id ~data:();
    Debug.show_node `G g.g_id;
    emit_all_nodes_ty (Lazy.force g.g_child) dict;
    Debug.show_edge `Structural g.g_id ((get_tyvar (UnionFind.get (Lazy.force g.g_child))).ty_id);
    begin match g.g_bound with
      | Some {b_ty; b_at = g'} ->
          Debug.show_edge (`Binding b_ty) g'.g_id g.g_id;
          emit_all_nodes_g g' dict
      | None ->
          Debug.set_root g.g_id
    end
  end
and emit_bind_edge n {b_at; b_ty} dict =
  match b_at with
  | `Ty parent ->
      let parent = Lazy.force parent in
      emit_all_nodes_ty parent dict;
      let p_id = (get_tyvar (UnionFind.get parent)).ty_id in
      Debug.show_edge (`Binding b_ty) p_id n
  | `G g ->
      emit_all_nodes_g g dict;
      Debug.show_edge (`Binding b_ty) g.g_id n


let render_graph cs =
  if Config.render_constraints then
    let visited = ref IntMap.empty in
    Debug.start_graph ();
    emit_all_nodes_ty cs.ty visited;
    List.iter cs.unification
      ~f:(fun (Unify(_, l, r)) ->
          let id n = (get_tyvar (UnionFind.get n)).ty_id in
          Debug.show_edge `Unify (id l) (id r);
          emit_all_nodes_ty l visited;
          emit_all_nodes_ty r visited
        );
    cs.instantiation
    |> Map.to_alist
    |> List.iter ~f:(fun (_, (g, ts)) ->
        emit_all_nodes_g g visited;
        List.iter ts ~f:(fun t ->
            let t_id = (get_tyvar (UnionFind.get t)).ty_id in
            Debug.show_edge `Instance g.g_id t_id;
            emit_all_nodes_ty t visited)
      );
    Debug.end_graph ()
  else
    ()
