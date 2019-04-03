open Typecheck_types
open Gensym

(* Helpers for signaling type errors *)
let typeErr e = raise (MuleErr.MuleExn (MuleErr.TypeError e))
let permErr op = typeErr (MuleErr.PermissionErr op)
let ctorErr l r = typeErr (MuleErr.MismatchedCtors (l, r))

let rec tyvar_bound_list: tyvar -> bound_ty list =
  fun {ty_bound; _} ->
    let {b_ty; b_at} = UnionFind.get ty_bound in
    match b_at with
    | `G g -> b_ty :: gnode_bound_list g
    | `Ty t -> b_ty :: ty_bound_list (UnionFind.get (Lazy.force t))
and ty_bound_list ty =
  tyvar_bound_list (get_tyvar ty)

let tyvar_permission: tyvar -> permission =
  fun tv ->
    get_permission (tyvar_bound_list tv)

let ty_permission: u_type -> permission =
  fun ty ->
    get_permission (ty_bound_list ty)

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
      Some (UnionFind.get (get_tyvar (UnionFind.get (Lazy.force u))).ty_bound)

(* Raise b one step, if it is legal to do so, otherwise throw an error. *)
let raised_bound b = match b with
  | {b_ty = `Rigid; _} ->
      permErr `Raise
  | _ ->
      bound_next b

(* Compute the least common ancestor of two bounds.
 * If that ancestor is not reachable without raising
 * past rigid edges, fail. *)
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
 * in-place. *)
let unify_tyvar: tyvar -> tyvar -> tyvar =
  fun l r ->
    UnionFind.merge unify_bound l.ty_bound r.ty_bound;
    l

let rec unify l r =
  (* First, work out what the tyvar for the final result will be. This has a
   * side effect of raising the two arguments' bounds until they agree,
   * weakening one of them to do so if needed.
   *)
  let tv = unify_tyvar (get_tyvar l) (get_tyvar r) in

  match l, r with
  | `Free {ty_id = lv; _}, `Free {ty_id = rv; _} when lv = rv ->
      (* same type variable; just return it *)
      l

  | ((`Free _) as v), t | t, ((`Free _) as v) ->
      (* Corresponds to "grafting" in {MLF-Graph-Unify}. Only valid for flexible
       * bottom vars. *)
      begin match ty_permission v with
        | F -> t
        | _ -> permErr `Graft
      end

  (* Neither side of these is a type variable, so we need to do a merge.
   * See the definition in section 3.2.2 of {MLF-Graph-Unify}. Before moving
   * forward, We need to make sure the merge is legal. We deal explicitly
   * with requirement 3 here; the other parts are sidestepped (see below).
   *
   * The call to unify_tyvar above ensures that the nodes' bounds and flags
   * are the same. The remaining part of requirement 3 is that the permissions
   * are not locked, so check for that, and fail if they are locked:
   *)
  | _ when perm_eq (tyvar_permission tv) L ->
      permErr `Merge

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
            ; ty_bound = UnionFind.make (get_u_bound (UnionFind.get v))
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
