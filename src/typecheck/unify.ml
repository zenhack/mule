open Typecheck_types
open Gensym

(* Helpers for signaling type errors *)
let typeErr e = raise (MuleErr.MuleExn (MuleErr.TypeError e))
let permErr op = typeErr (MuleErr.PermissionErr op)
let ctorErr l r = typeErr (MuleErr.MismatchedCtors (l, r))

(* Get the "permission" of a node, based on the node's binding path
 * (starting from the node and working up the tree). See section 3.1
 * in {MLF-Graph-Unify}. *)
let get_permission: (unit, bound_ty) Sequence.Generator.t -> permission =
  fun p ->
    let rec go p = match Sequence.next p with
    | None -> F
    | Some (`Rigid, _) -> R
    | Some (`Flex, bs) ->
        begin match go bs with
          | F -> F
          | R | L -> L
        end
    in go (Sequence.Generator.run p)

let rec gnode_bound_list: g_node -> (unit, bound_ty) Sequence.Generator.t =
  fun {g_bound; _} -> Sequence.Generator.(
    match g_bound with
    | None -> return ()
    | Some {b_ty; b_at} ->
        yield b_ty >>= fun () -> gnode_bound_list b_at
)
let rec tyvar_bound_list: tyvar -> (unit, bound_ty) Sequence.Generator.t =
  fun {ty_bound; _} -> bound_list !ty_bound
and tgt_bound_list = function
  | `G g -> gnode_bound_list g
  | `Ty t -> ty_bound_list (UnionFind.get (Lazy.force t))
and bound_list {b_ty; b_at} =
  Sequence.Generator.(
    yield b_ty >>= fun () -> tgt_bound_list b_at
  )
and ty_bound_list ty =
  tyvar_bound_list (get_tyvar ty)

let tyvar_permission: tyvar -> permission =
  fun tv ->
    get_permission (tyvar_bound_list tv)

let bound_permission: bound_target bound -> permission =
  fun b -> get_permission (bound_list b)

let b_at_id = function
  | `G {g_id; _} -> g_id
  | `Ty u -> (get_tyvar (UnionFind.get (Lazy.force u))).ty_id

let bound_id {b_at; _} = b_at_id b_at

let bound_next {b_at; _} = match b_at with
  | `G {g_bound; _} ->
      begin match g_bound with
        | None -> None
        | Some {b_ty; b_at = g} -> Some
            { b_ty
            ; b_at = `G g
            }
      end
  | `Ty u ->
      Some !((get_tyvar (UnionFind.get (Lazy.force u))).ty_bound)

(* Raise b one step, if it is legal to do so, otherwise throw an error. *)
let raised_bound b =
  match bound_permission b with
    | L -> permErr `Raise
    | _ -> bound_next b

(* Compute the least common ancestor of two bounds.
 * If that ancestor is not reachable without performing
 * illegal raisings, fail. *)
let rec bound_lca: bound_target bound -> bound_target bound -> bound_target bound =
  fun l r ->
    let lid, rid = bound_id l, bound_id r in
    if lid = rid then
      l
    else if lid < rid then
      begin match raised_bound r with
        | Some b -> bound_lca l b
        | None -> failwith "No LCA!"
      end
    else
      begin match raised_bound l with
        | Some b -> bound_lca b r
        | None -> failwith "No LCA!"
      end

(* "Unify" two binding edges. This does a combination of raising and
 * weakening as needed to make them the same. It does not modify anything,
 * but rather returns the new common bound.*)
let unify_bound l r =
  let {b_at; _} = bound_lca l r in
  match l.b_ty, r.b_ty with
  | `Flex, `Flex -> {b_at; b_ty = `Flex}
  | _ -> {b_at; b_ty = `Rigid}

(* Thin wrapper around [unify_bound], which updates the [tyvar]s' bounds
 * in-place. It does *not* permanantly link them, in the way that
 * UnionFind.merge does.
 *)
let unify_tyvar: tyvar -> tyvar -> tyvar =
  fun l r ->
    let new_bound = unify_bound !(l.ty_bound) !(r.ty_bound) in
    l.ty_bound := new_bound;
    r.ty_bound := new_bound;
    l

let graft: u_type -> tyvar -> u_type = fun t v ->
  (* {MLF-Graph} describes grafting as the process of replacing a
   * flexible bottom node with another type. However, we only call this
   * in places where we're actually looking to merge the two graphs, so
   * it seems wasteful to actually do a copy first, since we're just
   * going to end up unifying them. Instead, we raise the binding edges
   * as needed until they meet those of the bottom node; this brings them
   * to the point where they would have to be to be merged with a hypothetical
   * mirror in the grafted tree. From here, the result of grafting and then
   * merging is the same as just unifying.
   *)

  (* In case we hit shared (or more importantly, recursive) nodes: *)
  let visited = ref IntSet.empty in

  let raise_tv tv =
    let _ = unify_tyvar tv v in
    ()
  in
  let rec raise_bounds: u_type -> unit = fun t ->
    let tv = get_tyvar t in
    if Set.mem !visited tv.ty_id then
      ()
    else
      begin
        visited := Set.add !visited tv.ty_id;
        raise_tv tv;
        match t with
        | `Free _ ->
            ()
        | `Fn(_, param, ret) ->
            raise_bounds (UnionFind.get param);
            raise_bounds (UnionFind.get ret);
        | `Record(_, r) -> raise_bounds_row (UnionFind.get r)
        | `Union(_, r) -> raise_bounds_row (UnionFind.get r)
      end
  and raise_bounds_row: u_row -> unit = fun r ->
    let tv = get_tyvar r in
    if Set.mem !visited tv.ty_id then
      ()
    else
      begin
        visited := Set.add !visited tv.ty_id;
        raise_tv tv;
        match r with
        | `Free _ -> ()
        | `Empty _ -> ()
        | `Extend(_, _, t, r) ->
            raise_bounds (UnionFind.get t);
            raise_bounds_row (UnionFind.get r)
      end
  in
  raise_bounds t;
  let _ = unify_tyvar (get_tyvar t) v in
  t

let rec unify l r =
  match l, r with
  | _ when (get_tyvar l).ty_id = (get_tyvar r).ty_id ->
      (* These are already the same node; just return one. *)
      l

  (* It is important that we do the graft permission checks *before*
   * any raisings/weakenings to get the bounds to match -- otherwise we
   * could get spurrious permission errors. *)
  | (`Free v), t when perm_eq (tyvar_permission v) F -> graft t v
  | t, (`Free v) when perm_eq (tyvar_permission v) F -> graft t v
  | (`Free _), _ | _, (`Free _) -> permErr `Graft

  | _ ->
  (* Neither side of these is a type variable, so we need to do a merge.
   * See the definition in section 3.2.2 of {MLF-Graph-Unify}. Before moving
   * forward, We need to make sure the merge is legal. We deal explicitly
   * with requirement 3 here; the other parts are sidestepped (see below).
   *
   * The call to unify_tyvar above ensures that the nodes' bounds and flags
   * are the same. The remaining part of requirement 3 is that the permissions
   * are not locked, so check for that, and fail if they are locked:
   *)
  let tv = unify_tyvar (get_tyvar l) (get_tyvar r) in
  if perm_eq (tyvar_permission tv) L then
    permErr `Merge
  else
    begin match l, r with
    | (`Free _), _ | _, (`Free _) ->
        (* This should have been ruled out above. TODO: refactor so this
         * fits more nicely with the exhaustiveness checker. *)
        failwith "Impossible"

    (* Top level type constructors that match. We recursively
     * merge the types in a bottom-up fashion. Doing this makes it
     * easy to see that the conditions for being a valid merge
     * are satisfied (See {MLF-Graph-Unify} section 3.2.2 for the
     * definition):
     *
     * - 1 & 2 are trivial, since the subgraphs are always identical.
     * - 3 is checked separately, above.
     * - 4 follows vaccuously from the fact that merging the roots
     *   will not cause any other nodes to be merged (since they already
     *   have been).
     *
     * For this argument to work it is important that we can consider
     * the merge of the roots not to have "started" until the subgraphs
     * are fully merged. The only threat to this is the fact that we
     * have modified the two roots above, in the call to [unify_tyvar].
     * However, the modifications that [unify_tyvar] makes are all legal
     * raisings and weakenings, so can be thought of as their own atomic
     * steps, not part of the merge.
     *)
    | (`Fn (_, ll, lr), `Fn (_, rl, rr)) ->
        UnionFind.merge unify ll rl;
        UnionFind.merge unify lr rr;
        `Fn (tv, ll, lr)
    | (`Record (_, row_l), `Record(_, row_r)) ->
        UnionFind.merge unify_row row_l row_r;
        `Record (tv, row_l)
    | (`Union (_, row_l), `Union(_, row_r)) ->
        UnionFind.merge unify_row row_l row_r;
        `Union(tv, row_l)


    (* Top level type constructors that _do not_ match. In this case
     * unfication fails.
     *
     * we could have a catchall, but this way we can give the user
     * a little more information, and even while it's a bit verbose
     * it also means that the compiler will catch if we miss a case
     * that should be handled differently. it would be nice to
     * refactor so we don't have to list every combination though.
     *)
    | `Fn     _, `Record _ -> ctorErr `Fn     `Record
    | `Fn     _, `Union  _ -> ctorErr `Fn     `Union
    | `Record _, `Fn     _ -> ctorErr `Record `Fn
    | `Record _, `Union  _ -> ctorErr `Record `Union
    | `Union  _, `Fn     _ -> ctorErr `Union  `Fn
    | `Union  _, `Record _ -> ctorErr `Union  `Record
    end
and unify_row l r =
  let tv = unify_tyvar (get_tyvar l) (get_tyvar r) in
  match l, r with
  | (`Empty _, `Empty _) -> `Empty tv
  | (`Extend (_, l_lbl, l_ty, l_rest), `Extend (_, r_lbl, r_ty, r_rest)) ->
      let ret = `Extend (tv, l_lbl, l_ty, l_rest) in
      if Ast.Label.equal l_lbl r_lbl then begin
        UnionFind.merge unify l_ty r_ty;
        UnionFind.merge unify_row l_rest r_rest;
        ret
      end else begin
        (* XXX: I(@zenhack) am not sure what the bounds should be here;
         * my rough intuition is that they should be the same as the
         * other row variable, but I need to think about the logic here
         * more carefully. This is the only place in the unification
         * algorithm where we actually generate new bottom nodes, and the
         * MLF papers don't talk about this since the stuff from {Records}
         * is an extension.
         *)
        let new_with_bound v =
          UnionFind.make (`Free
            { ty_id = gensym ()
            ; ty_bound = ref (get_u_bound (UnionFind.get v))
            })
        in
        let new_rest_r = new_with_bound r_rest in
        let new_rest_l = new_with_bound l_rest in
        let new_tv () =
          { ty_id = gensym ()
          ; ty_bound = tv.ty_bound
          }
        in
        UnionFind.merge unify_row
          r_rest
          (UnionFind.make (`Extend(new_tv (), l_lbl, l_ty, new_rest_r)));
        UnionFind.merge unify_row
          l_rest
          (UnionFind.make (`Extend(new_tv (), r_lbl, r_ty, new_rest_l)));
        ret
      end

  | (`Free _, r) -> r
  | (l, `Free _) -> l
  | (`Extend (_, lbl, _, _), `Empty _) -> ctorErr (`Extend lbl) `Empty
  | (`Empty _, `Extend (_, lbl, _, _)) -> ctorErr `Empty (`Extend lbl)
