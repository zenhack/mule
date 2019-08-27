open Typecheck_types
open Gensym

(* Helpers for signaling type errors *)
let typeErr e = MuleErr.throw (`TypeError e)
let permErr rsn op = typeErr (rsn, `PermissionErr op)
let ctorErr rsn l r = typeErr (rsn, `MismatchedCtors (l, r))

(* Get the "permission" of a node, based on the node's binding path
 * (starting from the node and working up the tree). See section 3.1
 * in {MLF-Graph-Unify}. *)
let get_permission: (unit, bound_ty) Sequence.Generator.t -> permission =
  fun p ->
  let rec go p = match Sequence.next p with
    | None -> F
    | Some (`Explicit, _) -> E
    | Some (`Rigid, _) -> R
    | Some (`Flex, bs) ->
        begin match go bs with
          | F -> F
          | R | L -> L
          | E -> MuleErr.bug
                ("explicit nodes should never have other nodes bound " ^
                 "on them.")
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
let raised_bound rsn b =
  match bound_permission b with
  | L -> permErr rsn `Raise
  | _ -> bound_next b

(* Compute the least common ancestor of two bounds.
 * If that ancestor is not reachable without performing
 * illegal raisings, fail. *)
let rec bound_lca: Types.reason -> bound_target bound -> bound_target bound -> bound_target bound =
  fun rsn l r ->
  let lid, rid = bound_id l, bound_id r in
  if lid = rid then
    l
  else
    begin match bound_permission l, bound_permission r with
      | E, _ | _, E | L, _ | _, L -> permErr rsn `Raise
      | _ when lid < rid ->
          begin match raised_bound rsn r with
            | Some b -> bound_lca rsn l b
            | None -> MuleErr.bug "No LCA!"
          end
      | _ ->
          begin match raised_bound rsn l with
            | Some b -> bound_lca rsn b r
            | None -> MuleErr.bug "No LCA!"
          end
    end

(* "Unify" two binding edges. This does a combination of raising and
 * weakening as needed to make them the same. It does not modify anything,
 * but rather returns the new common bound.*)
let unify_bound rsn l r =
  let {b_at; _} = bound_lca rsn l r in
  match l.b_ty, r.b_ty with
  | `Flex, `Flex -> {b_at; b_ty = `Flex}
  | `Flex, `Rigid | `Rigid, `Flex | `Rigid, `Rigid ->
      {b_at; b_ty = `Rigid}
  | `Flex, `Explicit | `Explicit, `Flex | `Explicit, `Explicit ->
      {b_at; b_ty = `Explicit}
  | `Rigid, `Explicit | `Explicit, `Rigid ->
      permErr rsn `Raise

(* Thin wrapper around [unify_bound], which updates the [tyvar]s' bounds
 * in-place. It does *not* permanantly link them, in the way that
 * UnionFind.merge does.
*)
let unify_tyvar: Types.reason -> tyvar -> tyvar -> tyvar =
  fun rsn l r ->
  let new_bound = unify_bound rsn !(l.ty_bound) !(r.ty_bound) in
  l.ty_bound := new_bound;
  r.ty_bound := new_bound;
  l

let raise_tv: Types.reason -> bound_target bound -> tyvar -> unit = fun rsn b tv ->
  let new_bound = unify_bound rsn !(tv.ty_bound) b in
  tv.ty_bound := new_bound

(* Raise the bounds for an entire subtree. *)
let rec raise_bounds: Types.reason -> bound_target bound -> IntSet.t -> IntSet.t ref -> u_type -> unit =
  fun rsn bound above visited t ->
  let tv = get_tyvar t in
  let bound_tgt_id =
    match (!(tv.ty_bound)).b_at with
    | `G {g_id; _} -> g_id
    | `Ty at ->
        let {ty_id; _} =
          Lazy.force at
          |> UnionFind.get
          |> get_tyvar
        in
        ty_id
  in
  if not (Set.mem !visited tv.ty_id) then begin
    visited := Set.add !visited tv.ty_id;
    if not (Set.mem above bound_tgt_id) then begin
      raise_tv rsn bound tv
    end;
    let new_above = Set.add above tv.ty_id in
    match t with
    | `Free _ -> ()
    | `Quant(_, arg) ->
        raise_bounds rsn bound new_above visited (UnionFind.get arg)
    | `Const(_, _, args, _) ->
        List.iter
          args
          ~f:(fun (ty, _) ->
              raise_bounds rsn bound new_above visited (UnionFind.get ty))
  end

let graft: Types.reason -> u_type -> tyvar -> u_type = fun rsn t v ->
  (* {MLF-Graph} describes grafting as the process of replacing a
   * flexible bottom node with another type. However, we only call this
   * in places where we're actually looking to merge the two graphs, so
   * it seems wasteful to actually do a copy first, since we're just
   * going to end up unifying them. Instead, we raise the binding edges
   * as needed until they meet that of the bottom node; this brings them
   * to the point where they would have to be to be merged with a hypothetical
   * mirror in the grafted tree. From here, the result of grafting and then
   * merging is the same as just unifying.
  *)
  raise_bounds rsn !(v.ty_bound) IntSet.empty (ref IntSet.empty) t;
  ignore (unify_tyvar rsn (get_tyvar t) v);
  t

let rec unify already_merged rsn l r =
  !Debug.render_hook ();
  let lid, rid = (get_tyvar l).ty_id, (get_tyvar r).ty_id in
  if lid = rid || Set.mem already_merged (lid, rid) then
    l
  else begin
    let already_merged = Set.add already_merged (lid, rid) in

    let merge_tv () =
      let tv = unify_tyvar rsn (get_tyvar l) (get_tyvar r) in
      if perm_eq (tyvar_permission tv) L then
        permErr rsn `Merge
      else
        tv
    in
    match l, r with
    (* It is important that we do the graft permission checks *before*
     * any raisings/weakenings to get the bounds to match -- otherwise we
     * could get spurrious permission errors. *)
    | (`Free (v, _)), t when perm_eq (tyvar_permission v) F -> graft rsn t v
    | t, (`Free (v, _)) when perm_eq (tyvar_permission v) F -> graft rsn t v
    | (`Free _), _ | _, (`Free _) -> permErr rsn `Graft

    (* Neither side of these is a type variable, so we need to do a merge.
     * See the definition in section 3.2.2 of {MLF-Graph-Unify}. *)
    | `Quant(_, argl), `Quant(_, argr) ->
        normalize_unify
          already_merged
          (`Cascade(rsn, 1))
          argl
          argr;
        `Quant(merge_tv (), argl)

    | `Quant _, `Const _ | `Const _, `Quant _ ->
        MuleErr.bug "normalization left quant & const paired."
    | `Const(_, cl, argsl, k), `Const(_, cr, argsr, _) ->
        if typeconst_eq cl cr then
          (* Top level type constructors that match. We recursively
           * merge the types in a bottom-up fashion. Doing this makes it
           * easy to see that the conditions for being a valid merge
           * are satisfied:
           *
           * - 1 & 2 are trivial, since the subgraphs are always identical.
           * - 3 is enforced/checked by merge_tv ().
           * - 4 follows vaccuously from the fact that merging the roots
           *   will not cause any other nodes to be merged (since they already
           *   have been).
           *
           * For this argument to work it is important that we can consider
           * the merge of the roots not to have "started" until the subgraphs
           * are fully merged -- so we must be careful not to violate this
           * invariant.
          *)
          begin
            let args_i_l = List.mapi argsl ~f:(fun i v -> (i, v)) in
            List.iter2_exn args_i_l argsr
              ~f:(fun (i, (l, _)) (r, _) ->
                  normalize_unify
                    already_merged
                    (`Cascade(rsn, i+1))
                    l
                    r
                );
            `Const(merge_tv (), cl, argsl, k)
          end
        else
          begin match cl, argsl, cr, argsr with
            (* Mismatched extend constructors get treated specially, because of the
             * equivalence relation on rows. *)
            | `Extend l_lbl, [l_ty, _; l_rest, _], `Extend r_lbl, [r_ty, _; r_rest, _] ->
                begin
                  (* Extend nodes are always inert, so the exact bounds we choose
                   * for the new nodes don't really matter, as long as the resulting
                   * graph is well-formed. *)
                  let new_with_bound v =
                    UnionFind.make
                      (`Free
                         ( { ty_id = gensym ()
                           ; ty_bound = ref (get_u_bound (UnionFind.get v))
                           }
                         , kvar_row
                         )
                      )
                  in
                  let new_rest_r = new_with_bound r_rest in
                  let new_rest_l = new_with_bound l_rest in
                  let new_tv () =
                    { ty_id = gensym ()
                    ; ty_bound = (get_tyvar l).ty_bound
                    }
                  in
                  normalize_unify already_merged
                    (`ExtendTail (rsn, `L))
                    r_rest
                    (UnionFind.make (extend (new_tv ()) l_lbl l_ty new_rest_r));
                  normalize_unify already_merged
                    (`ExtendTail (rsn, `R))
                    l_rest
                    (UnionFind.make (extend (new_tv ()) r_lbl r_ty new_rest_l));
                end;
                extend (merge_tv ()) l_lbl l_ty l_rest
            | _ ->
                (* Top level type constructors that _do not_ match. In this case
                 * unfication fails. *)
                ctorErr rsn cl cr
          end
  end
(* Wrapper around UnionFind.merge/unify that first normalizes the arguments. *)
and normalize_unify already_merged rsn l r =
  let l, r = Normalize.pair l r in
  UnionFind.merge (unify already_merged rsn) l r

let unify = unify IntPairSet.empty
let normalize_unify = normalize_unify IntPairSet.empty
