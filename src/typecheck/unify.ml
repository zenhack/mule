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

let raise_tv: bound_target bound -> tyvar -> unit = fun b tv ->
  let new_bound = unify_bound !(tv.ty_bound) b in
  tv.ty_bound := new_bound

(* Raise the bounds for an entire subtree. *)
let rec raise_bounds: bound_target bound -> IntSet.t ref -> u_type -> unit =
  fun bound visited t ->
    let tv = get_tyvar t in
    if Set.mem !visited tv.ty_id then
      ()
    else
      begin
        visited := Set.add !visited tv.ty_id;
        raise_tv bound tv;
        match t with
        | `Free _ -> ()
        | `Quant(_, arg) ->
            raise_bounds bound visited (UnionFind.get arg)
        | `Const(_, _, args, _) ->
            List.iter
              args
              ~f:(fun (ty, _) ->
                    raise_bounds bound visited (UnionFind.get ty))
      end

let graft: u_type -> tyvar -> u_type = fun t v ->
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
  raise_bounds !(v.ty_bound) (ref IntSet.empty) t;
  ignore (unify_tyvar (get_tyvar t) v);
  t

let rec unify already_merged l r =
  let lid, rid = (get_tyvar l).ty_id, (get_tyvar r).ty_id in
  if lid = rid || Set.mem already_merged (lid, rid) then l else
  let already_merged = Set.add already_merged (lid, rid) in

  let merge_tv () =
    let tv = unify_tyvar (get_tyvar l) (get_tyvar r) in
    if perm_eq (tyvar_permission tv) L then
      permErr `Merge
    else
      tv
  in
  match l, r with
  (* It is important that we do the graft permission checks *before*
   * any raisings/weakenings to get the bounds to match -- otherwise we
   * could get spurrious permission errors. *)
  | (`Free (v, _)), t when perm_eq (tyvar_permission v) F -> graft t v
  | t, (`Free (v, _)) when perm_eq (tyvar_permission v) F -> graft t v
  | (`Free _), _ | _, (`Free _) -> permErr `Graft

  (* Neither side of these is a type variable, so we need to do a merge.
   * See the definition in section 3.2.2 of {MLF-Graph-Unify}. *)
  | `Quant(_, argl), `Quant(_, argr) ->
      whnf_unify already_merged argl argr;
      `Quant(merge_tv (), argl)

  | `Quant _, `Const _ | `Const _, `Quant _ ->
      (* quantifiers and constructors should interleave, so we should never have
       * them paired. *)
      failwith "Impossible"

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
          List.iter2_exn argsl argsr
            ~f:(fun (l, _) (r, _) -> whnf_unify already_merged l r);
          `Const(merge_tv (), cl, argsl, k)
        end
      else
        begin match cl, argsl, cr, argsr with
        (* Mismatched extend constructors get treated specially, because of the
         * equivalence relation on rows. *)
        | `Extend l_lbl, [l_ty, _; l_rest, _], `Extend r_lbl, [r_ty, _; r_rest, _] ->
            begin
              (* XXX: I(@zenhack) am not sure what the bounds should be here;
               * my rough intuition is that they should be the same as the
               * other row variable, but I need to think about the logic here
               * more carefully. This is the only place in the unification
               * algorithm where we actually generate new bottom nodes, and the
               * MLF papers don't talk about this since the stuff from {Records}
               * is an extension.
               *)
              let new_with_bound v =
                UnionFind.make
                  (`Free
                    ( { ty_id = gensym ()
                      ; ty_bound = ref (get_u_bound (UnionFind.get v))
                      }
                    , `Row
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
              whnf_unify already_merged
                r_rest
                (UnionFind.make (extend (new_tv ()) l_lbl l_ty new_rest_r));
              whnf_unify already_merged
                l_rest
                (UnionFind.make (extend (new_tv ()) r_lbl r_ty new_rest_l));
            end;
            extend (merge_tv ()) l_lbl l_ty l_rest
        | _ ->
          (* Top level type constructors that _do not_ match. In this case
           * unfication fails. *)
          ctorErr cl cr
        end
(* Wrapper around UnionFind.merge/unify that first reduces the arguments to whnf. *)
and whnf_unify already_merged l r =
  UnionFind.merge (unify already_merged) (Normalize.whnf l) (Normalize.whnf r)
let unify = unify IntPairSet.empty
