module MkMap(Key:Comparator.S) = struct
  type 'a t = (Key.t, 'a, Key.comparator_witness) Map.t
end

module Env = MkMap(Ast.Var)

module IntMap = MkMap(Int)

open Ast.Desugared
open Gensym
open OrErr

(* The type of values associated with unification variables *)
type u_type =
  | Type of tyvar
  | Fn of (tyvar * u_type UnionFind.var * u_type UnionFind.var)
  | Record of (tyvar * u_row UnionFind.var)
  | Union of (tyvar * u_row UnionFind.var)
and u_row =
  | Extend of (tyvar * Ast.Label.t * u_type UnionFind.var * u_row UnionFind.var)
  | Empty of tyvar
  | Row of tyvar
and bound_ty = [ `Rigid | `Flex ]
and bound = {
  b_ty: bound_ty;
  b_at: bound_target;
}
and tyvar =
  { ty_id: int
  ; mutable ty_bound: bound
  }
and g_node = {
  g_id: int;
  g_bound: (bound_ty * g_node) option;
  g_child: u_type UnionFind.var Lazy.t;
}
and bound_target =
  [ `Ty of u_type UnionFind.var
  | `G of g_node
  ]

type permission = F | R | L

let perm_eq: permission -> permission -> bool = Poly.equal

(* Helpers for signaling type errors *)
let typeErr e = raise (MuleErr.MuleExn (MuleErr.TypeError e))
let permErr op = typeErr (MuleErr.PermissionErr op)
let ctorErr l r = typeErr (MuleErr.MismatchedCtors (l, r))

let with_g
  : ((bound_ty * g_node) option)
  -> (g_node Lazy.t -> u_type UnionFind.var)
  -> (g_node * u_type UnionFind.var)
  = fun parent f ->
      let gid = gensym () in
      let rec g = lazy {
        g_id = gid;
        g_bound = parent;
        g_child = ret;
      }
      and ret = lazy (f g)
      in (Lazy.force g, Lazy.force ret)

(* Get the "permission" of a node, based on the node's binding path
 * (starting from the node and working up the tree). See section 3.1
 * in {MLF-Graph-Unify}. *)
let rec get_permission: bound_ty list -> permission = function
  | [] -> F
  | (`Rigid :: _) -> R
  | (`Flex :: bs) ->
      begin match get_permission bs with
        | F -> F
        | R | L -> L
      end

let rec gnode_bound_list {g_bound; _} = match g_bound with
  | None -> []
  | Some (b_ty, g) -> b_ty :: gnode_bound_list g
let get_tyvar: u_type -> tyvar = function
  | Type v -> v
  | Fn (v, _, _) -> v
  | Record (v, _) -> v
  | Union (v, _) -> v
let get_ty_bound: u_type -> bound =
  fun ty -> ((get_tyvar ty).ty_bound)
let get_row_var: u_row -> tyvar = function
  | Extend(v, _, _, _) -> v
  | Empty v -> v
  | Row v -> v
let get_row_bound: u_row -> bound =
  fun r -> ((get_row_var r).ty_bound)

let rec show_u_type_v s v =
  let t = UnionFind.get v in
  let n = (get_tyvar t).ty_id in
  if Set.mem s n then
    "t" ^ Int.to_string n
  else
    let s = Set.add s n in
    match t with
    | Type _ -> "t" ^ Int.to_string n
    | Fn (_, l, r) ->
        "(" ^ show_u_type_v s l ^ " -> " ^ show_u_type_v s r ^ ")"
    | Record(_, row) ->
        "Record{" ^ show_u_row_v s row ^ "}"
    | Union(_, row) ->
        "Union(" ^ show_u_row_v s row ^ ")"
and show_u_row_v s v =
  let r = UnionFind.get v in
  let n = (get_row_var r).ty_id in
  if Set.mem s n then
    "r" ^ Int.to_string n
  else
    let s = Set.add s n in
    match r with
    | Row {ty_id; _} ->
        "r" ^ Int.to_string ty_id
    | Empty _ ->
        "<empty>"
    | Extend (_, lbl, ty, rest) ->
        "(" ^ Ast.Label.to_string lbl ^ " => " ^ show_u_type_v s ty ^ ") :: " ^ show_u_row_v s rest
let show_u_type_v = show_u_type_v (Set.empty (module Int))
let show_u_row_v  = show_u_row_v  (Set.empty (module Int))

let show_g {g_child; _} =
  show_u_type_v (Lazy.force g_child)

let rec in_constraint_interior: g_node -> bound -> bool =
  fun g child -> begin match child.b_at with
    | `Ty t ->
        in_constraint_interior g ((get_tyvar (UnionFind.get t)).ty_bound)
    | `G g' ->
        if g.g_id = g'.g_id then
          true
        else begin match g'.g_bound with
          | None -> false
          | Some (b_ty, next) ->
              in_constraint_interior g { b_ty; b_at = `G next }
        end
  end

let rec tyvar_bound_list: tyvar -> bound_ty list =
  fun {ty_bound = {b_ty; b_at}; _} ->
    match b_at with
    | `G g -> b_ty :: gnode_bound_list g
    | `Ty t -> b_ty :: ty_bound_list (UnionFind.get t)
and ty_bound_list ty =
  tyvar_bound_list (get_tyvar ty)

let tyvar_permission: tyvar -> permission =
  fun tv ->
    get_permission (tyvar_bound_list tv)

let ty_permission: u_type -> permission =
  fun ty ->
    get_permission (ty_bound_list ty)

type constraint_ops =
  { constrain_ty   : u_type UnionFind.var -> u_type UnionFind.var -> unit
  ; constrain_row  : u_row UnionFind.var  -> u_row UnionFind.var  -> unit
  ; constrain_inst : g_node -> u_type UnionFind.var -> unit
  }

let gen_ty_var: g_node -> tyvar = fun g ->
  { ty_id = gensym ()
  ; ty_bound =
    { b_ty = `Flex
    ; b_at = `G g
    }
  }


let gen_ty_u: bound_target -> u_type UnionFind.var = fun targ ->
  UnionFind.make (Type
    { ty_id = gensym()
    ; ty_bound =
      { b_ty = `Flex
      ; b_at = targ
      }
    })
let gen_row_u: bound_target -> u_row UnionFind.var = fun targ ->
  UnionFind.make (Row
    { ty_id = gensym()
    ; ty_bound = {b_ty = `Flex; b_at = targ}
    })

let gen_ty_u_g g =
  UnionFind.make (Type (gen_ty_var g))


let b_at_id = function
  | `G {g_id; _} -> g_id
  | `Ty u -> (get_tyvar (UnionFind.get u)).ty_id

let bound_id {b_at; _} = b_at_id b_at

let bound_next {b_at; _} = match b_at with
  | `G {g_bound; _} ->
      begin match g_bound with
        | None -> None
        | Some (bty, g) -> Some
            { b_ty = bty
            ; b_at = `G g
            }
      end
  | `Ty u ->
      Some ((get_tyvar (UnionFind.get u)).ty_bound)

(* Raise b one step, if it is legal to do so, otherwise throw an error. *)
let raised_bound b = match b with
  | {b_ty = `Rigid; _} ->
      permErr `Raise
  | _ ->
      bound_next b

(* Compute the least common ancestor of two bounds.
 * If that ancestor is not reachable without raising
 * past rigid edges, fail. *)
let rec bound_lca: bound -> bound -> bound =
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
    let new_bound = unify_bound l.ty_bound r.ty_bound in
    l.ty_bound <- new_bound;
    r.ty_bound <- new_bound;
    l

let rec unify l r =
  (* First, work out what the tyvar for the final result will be. This has a
   * side effect of raising the two arguments' bounds until they agree,
   * weakening one of them to do so if needed.
   *)
  let tv = unify_tyvar (get_tyvar l) (get_tyvar r) in

  match l, r with
  | Type {ty_id = lv; _}, Type {ty_id = rv; _} when lv = rv ->
      (* same type variable; just return it *)
      l

  | ((Type _) as v), t | t, ((Type _) as v) ->
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
  | (Fn (_, ll, lr), Fn (_, rl, rr)) ->
      UnionFind.merge unify ll rl;
      UnionFind.merge unify lr rr;
      Fn (tv, ll, lr)
  | (Record (_, row_l), Record(_, row_r)) ->
      UnionFind.merge unify_row row_l row_r;
      Record (tv, row_l)
  | (Union (_, row_l), Union(_, row_r)) ->
      UnionFind.merge unify_row row_l row_r;
      Union(tv, row_l)


  (* Top level type constructors that _do not_ match. In this case
   * unfication fails.
   *
   * we could have a catchall, but this way we can give the user
   * a little more information, and even while it's a bit verbose
   * it also means that the compiler will catch if we miss a case
   * that should be handled differently. it would be nice to
   * refactor so we don't have to list every combination though.
   *)
  | Fn     _, Record _ -> ctorErr `Fn     `Record
  | Fn     _, Union  _ -> ctorErr `Fn     `Union
  | Record _, Fn     _ -> ctorErr `Record `Fn
  | Record _, Union  _ -> ctorErr `Record `Union
  | Union  _, Fn     _ -> ctorErr `Union  `Fn
  | Union  _, Record _ -> ctorErr `Union  `Record
and unify_row l r =
  let tv = unify_tyvar (get_row_var l) (get_row_var r) in
  match l, r with
  | (Empty _, Empty _) -> Empty tv
  | (Extend (_, l_lbl, l_ty, l_rest), Extend (_, r_lbl, r_ty, r_rest)) ->
      let ret = Extend (tv, l_lbl, l_ty, l_rest) in
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
          UnionFind.make (Row
            { ty_id = gensym ()
            ; ty_bound = get_row_bound (UnionFind.get v)
            })
        in
        let new_rest_r = new_with_bound r_rest in
        let new_rest_l = new_with_bound l_rest in

        UnionFind.merge unify_row
          r_rest
          (UnionFind.make (Extend(tv, l_lbl, l_ty, new_rest_r)));
        UnionFind.merge unify_row
          l_rest
          (UnionFind.make (Extend(tv, r_lbl, r_ty, new_rest_l)));
        ret
      end

  | (Row _, r) -> r
  | (l, Row _) -> l
  | (Extend (_, lbl, _, _), Empty _) -> ctorErr (`Extend lbl) `Empty
  | (Empty _, Extend (_, lbl, _, _)) -> ctorErr `Empty (`Extend lbl)

let rec walk cops env g = function
  | Expr.Var v ->
      let tv = gen_ty_u_g g in
      begin match Map.find_exn env v with
        | `Ty tv' ->
            cops.constrain_ty tv' tv
        | `G g' ->
            cops.constrain_inst g' tv
      end;
      tv
  | Expr.Lam (param, body) ->
      let param_var = gen_ty_u_g g in
      let ret_var = gen_ty_u_g g in
      let f_var = UnionFind.make(Fn (gen_ty_var g, param_var, ret_var)) in
      let (g_body, _) =
        with_g
          (Some (`Flex, g))
          (fun g -> walk
            cops
            (Map.set env ~key:param ~data:(`Ty param_var))
            (Lazy.force g)
            body)
      in
      cops.constrain_inst g_body ret_var;
      f_var
  | Expr.Let(v, e, body) ->
      let (g_e, _) = with_g
        (Some(`Flex, g))
        (fun g -> walk cops env (Lazy.force g) e)
      in
      walk cops (Map.set env ~key:v ~data:(`G g_e)) g body
  | Expr.App (f, arg) ->
      let param_var = gen_ty_u_g g in
      let ret_var = gen_ty_u_g g in
      let f_var = UnionFind.make(Fn (gen_ty_var g, param_var, ret_var)) in
      let (g_f, _) = with_g
        (Some(`Flex, g))
        (fun g -> walk cops env (Lazy.force g) f)
      in
      cops.constrain_inst g_f f_var;
      let (g_arg, _) = with_g
        (Some(`Flex, g))
        (fun g -> walk cops env (Lazy.force g) arg)
      in
      cops.constrain_inst g_arg param_var;
      ret_var
  | Expr.EmptyRecord ->
      UnionFind.make (Record (gen_ty_var g, UnionFind.make (Empty(gen_ty_var g))))
  | Expr.GetField (e, lbl) ->
      let tyvar = walk cops env g e in
      let rowVar = UnionFind.make (Row (gen_ty_var g)) in
      let recVar = UnionFind.make (Record (gen_ty_var g, rowVar)) in
      cops.constrain_ty recVar tyvar;
      let tailVar = UnionFind.make (Row (gen_ty_var g)) in
      let fieldVar = gen_ty_u_g g in
      cops.constrain_row
        rowVar
        (UnionFind.make (Extend(gen_ty_var g, lbl, fieldVar, tailVar)));
      fieldVar
  | Expr.Update (r, lbl, ty) ->
      let head_var = walk cops env g ty in
      let tail_var = UnionFind.make(Row(gen_ty_var g)) in
      let orig_var = walk cops env g r in
      let updated_var = UnionFind.make (Extend(gen_ty_var g, lbl, head_var, tail_var)) in
      cops.constrain_ty
          orig_var
          (UnionFind.make (Record (gen_ty_var g, tail_var)));
      UnionFind.make (Record (gen_ty_var g, updated_var))
  | Expr.Ctor (lbl, param) ->
      let uVar = gen_ty_var g in
      let paramVar = walk cops env g param in
      UnionFind.make
        ( Union
          ( uVar
          , UnionFind.make
            ( Extend
                ( gen_ty_var g
                , lbl
                , paramVar
                , UnionFind.make (Row (gen_ty_var g))
                )
            )
          )
        )
  | Expr.Match {cases; default} when Map.is_empty cases ->
      begin match default with
        | None -> raise (MuleErr.MuleExn EmptyMatch)
        | Some (Some paramVar, body) ->
            walk cops env g (Expr.Lam (paramVar, body))
        | Some (None, body) ->
            walk cops env g (Expr.Lam (Ast.Var.of_string "_", body))
      end
  | Expr.Match {cases; default} ->
      let final = match default with
        | None -> UnionFind.make (Empty (gen_ty_var g))
        | Some _ -> UnionFind.make (Row (gen_ty_var g))
      in
      let (rowVar, bodyVar) = walk_match cops env g final (Map.to_alist cases) in
      UnionFind.make
        ( Fn
            ( gen_ty_var g
            , UnionFind.make (Union(gen_ty_var g, rowVar))
            , bodyVar
            )
        )
  | Expr.WithType(v, _ty) ->
      (* TODO *)
      walk cops env g v
and walk_match cops env g final = function
  | [] -> (final, gen_ty_u_g g)
  | ((lbl, (var, body)) :: rest) ->
      let ty = gen_ty_u_g g in
      let bodyVar = walk cops (Map.set env ~key:var ~data:(`Ty ty)) g body in
      let (row, body') = walk_match cops env g final rest in
      cops.constrain_ty bodyVar body';
      ( UnionFind.make (Extend(gen_ty_var g, lbl, ty, row))
      , bodyVar
      )

let ivar i = Ast.Var.of_string ("t" ^ Int.to_string i)

let maybe_add_rec i vars ty =
  let myvar = ivar i in
  if Set.mem vars myvar then
    ( Set.remove vars myvar
    , Type.Recur(i, myvar, ty)
    )
  else
    (vars, ty)

let rec add_rec_binders ty =
  match ty with
  | Type.Var (_, v) ->
      ( Set.singleton (module Ast.Var) v
      , ty
      )
  | Type.Recur(i, v, t) ->
      let (vs, ts) = add_rec_binders t in
      ( Set.remove vs (ivar i)
      , Type.Recur(i, v, ts)
      )
  | Type.Fn (i, f, x) ->
      let (fv, ft) = add_rec_binders f in
      let (xv, xt) = add_rec_binders x in
      maybe_add_rec i (Set.union fv xv) (Type.Fn(i, ft, xt))
  | Type.Record(i, fields, rest) ->
      let (vars, ret) = row_add_rec_binders i fields rest in
      maybe_add_rec i vars (Type.Record ret)
  | Type.Union(i, ctors, rest) ->
      let (vars, ret) = row_add_rec_binders i ctors rest in
      maybe_add_rec i vars (Type.Union ret)
  | Type.All(i, bound, body) ->
      let (vars, body') = add_rec_binders body in
      maybe_add_rec i vars (Type.All(i, bound, body'))
and row_add_rec_binders i fields rest =
  let row_var = match rest with
    | Some v -> Set.singleton (module Ast.Var) v
    | None -> Set.empty (module Ast.Var)
  in
  let fields_vars =
    List.map fields ~f:(fun (lbl, ty) -> (lbl, add_rec_binders ty))
  in
  let vars = List.fold_left fields_vars
    ~init:row_var
    ~f:(fun accum (_, (vars, _)) -> Set.union accum vars)
  in
  let fields' = List.map fields_vars ~f:(fun (lbl, (_, ty)) -> (lbl, ty)) in
  (vars, (i, fields', rest))
let add_rec_binders ty =
  snd (add_rec_binders ty)

(* Extract a type from a (solved) unification variable. *)
let rec get_var_type env = function
  | Type {ty_id = i; _} -> Type.Var (i, (ivar i))
  | Fn ({ty_id = i; ty_bound = b}, f, x) ->
      if Set.mem env (ivar i) then
        get_var_type env (Type {ty_id = i; ty_bound = b})
      else
        let env' = Set.add env (ivar i) in
        Fn
          ( i
          , get_var_type env' (UnionFind.get f)
          , get_var_type env' (UnionFind.get x)
          )
  | Record ({ty_id = i; _}, fields) ->
      let (fields, rest) =
        get_var_row (Set.add env (ivar i)) (UnionFind.get fields)
      in
      Type.Record (i, fields, rest)
  | Union ({ty_id = i; _}, ctors) ->
      let (ctors, rest) =
        get_var_row (Set.add env (ivar i)) (UnionFind.get ctors)
      in
      Type.Union (i, ctors, rest)
and get_var_row env = function
  | Row {ty_id = i; _} -> ([], Some (ivar i))
  | Empty _ -> ([], None)
  | Extend (_, lbl, ty, rest) ->
      let (fields, rest) = get_var_row env (UnionFind.get rest) in
      ( ( lbl
        , get_var_type env (UnionFind.get ty)
        )
        :: fields
      , rest
      )
let get_var_type uvar =
  UnionFind.get uvar
    |> get_var_type (Set.empty (module Ast.Var))
    |> add_rec_binders

type unify_edge =
  | UnifyTypes of (u_type UnionFind.var * u_type UnionFind.var)
  | UnifyRows of (u_row UnionFind.var * u_row UnionFind.var)

type inst_edge =
  { ie_g_node: g_node
  ; ie_ty_node: u_type UnionFind.var
  }


let inst_bound: inst_edge -> g_node =
  fun {ie_ty_node; _} ->
    let rec go u =
      let bound = (get_tyvar (UnionFind.get u)).ty_bound in
      match bound.b_at with
      | `Ty u' -> go u'
      | `G g -> g
    in
    go ie_ty_node


let top_sort_inst: (g_node * (u_type UnionFind.var list)) IntMap.t -> (g_node * u_type UnionFind.var list) list
  = fun d ->
      let visited = ref (Set.empty (module Int)) in
      let accum = ref [] in
      let rec go (g, ts) =
        if Set.mem !visited g.g_id then
          ()
        else begin
          List.iter ts ~f:(fun t ->
            let g' = inst_bound
              { ie_ty_node = t
              ; ie_g_node = g
              }
            in
            if Set.mem !visited g'.g_id then
              ()
            else
              begin match Map.find d g'.g_id with
                | Some v ->
                    visited := Set.add !visited g'.g_id;
                    go v;
                    accum := v :: !accum
                | None -> ()
              end
          )
        end
      in
      Map.iter d ~f:go;
      Map.iteri d ~f:(fun ~key ~data ->
          if not (Set.mem !visited key) then
            (* This will happen for our top-level nodes, which don't
             * have any edges pointing into them. *)
            accum := data :: !accum
          else
            ()
      );
      !accum

type built_constraints =
  { unification: unify_edge list
  ; instantiation: (g_node * (u_type UnionFind.var) list) IntMap.t
  ; ty: u_type UnionFind.var
  }

let make_cops: unit ->
  ( constraint_ops
  * (unify_edge list) ref
  * ((g_node * (u_type UnionFind.var) list) IntMap.t) ref
  ) = fun () ->
  let report = Debug.report Config.dump_constraints in
  let ucs = ref [] in (* unification constraints *)
  let ics = ref (Map.empty (module Int)) in (* instantiation constraints *)
  let cops =
    { constrain_ty   =
      (fun l r ->
        report (fun () -> "constrain types: "
          ^ show_u_type_v l
          ^ " = "
          ^ show_u_type_v r);
        ucs := UnifyTypes(l, r) :: !ucs)
    ; constrain_row  = (fun l r ->
        report (fun () -> "constrain rows: "
            ^ show_u_row_v l
            ^ " = "
            ^ show_u_row_v r);
          ucs := UnifyRows(l, r) :: !ucs)
    ; constrain_inst =
        begin fun g t ->
          report
            (fun () -> "constrain_inst: "
              ^ show_u_type_v t
              ^ " <: "
              ^ show_g g);
          ics := Map.update !ics g.g_id ~f:(function
              | None -> (g, [t])
              | Some (_, ts) -> (g, (t :: ts))
            )
        end
    }
  in (cops, ucs, ics)


let build_constraints: Expr.t -> built_constraints = fun expr ->
  let cops, ucs, ics = make_cops () in
  let (_, ty) =
    with_g None begin fun g ->
      walk cops (Map.empty (module Ast.Var)) (Lazy.force g) expr
    end
  in
  { unification = !ucs
  ; instantiation = !ics
  ; ty = ty
  }

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
    let visited_types = ref (Map.empty (module Int)) in
    let visited_rows = ref (Map.empty (module Int)) in

    (* Generate the unification variable for the root up front, so it's
     * visible everywhere. *)
    let new_root_tv =
      { ty_id = gensym ()
      ; ty_bound =
        { b_ty = `Flex
        ; b_at = `G new_g
        }
      }
    in
    let new_root = gen_ty_u (`G new_g) in

    (* XXX: go and go_row have too much redundancy *)
    let rec go = fun nv ->
      let n = UnionFind.get nv in
      let {ty_id = old_id; ty_bound = old_bound} = get_tyvar n in
      begin match Map.find !visited_types old_id with
        | Some new_node -> new_node
        | None ->
            if not (in_constraint_interior old_g old_bound) then
              begin
                (* We've hit the frontier; replace it with a bottom node and
                 * constrain it to be equal to the old thing. *)
                let new_var = gen_ty_u (`G new_g) in
                cops.constrain_ty nv new_var;
                new_var
              end
            else
              (* First, generate the new bound. *)
              let new_tyvar =
                if UnionFind.equal nv old_root then
                  new_root_tv
                else
                  { ty_id = gensym ()
                  ; ty_bound =
                    { b_ty = old_bound.b_ty
                    ; b_at = `Ty new_root
                    }
                  }
              in

              (* Add a copy to the map up front, in case we hit a recursive type.
               * We'll have to unify it with the final result below. *)
              let map_copy =
                if UnionFind.equal nv old_root then
                  new_root
                else
                  UnionFind.make (Type {ty_id = gensym (); ty_bound = new_tyvar.ty_bound })
              in
              visited_types := Map.set !visited_types ~key:old_id ~data:map_copy;

              (* Now do a deep copy, subbing in the new bound. *)
              let ret = UnionFind.make (match n with
                | Type _ -> Type new_tyvar
                | Fn (_, param, ret) -> Fn(new_tyvar, go param, go ret)
                | Record(_, row) -> Record(new_tyvar, go_row row)
                | Union(_, row) -> Union(new_tyvar, go_row row))
              in
              UnionFind.merge unify map_copy ret;
              ret
      end

    and go_row row_var =
      let row = UnionFind.get row_var in
      let {ty_id = old_id; ty_bound = old_bound} = get_row_var row in
      begin match Map.find !visited_rows old_id with
        | Some new_node -> new_node
        | None ->
            let new_var =
              { ty_id = gensym ()
              ; ty_bound =
                { b_ty = old_bound.b_ty
                ; b_at = `Ty new_root
                }
              }
            in
            let map_copy =
              UnionFind.make (Row {ty_id = gensym (); ty_bound = new_var.ty_bound })
            in
            visited_rows := Map.set !visited_rows ~key:old_id ~data:map_copy;
            if not (in_constraint_interior old_g old_bound) then
              (* On the frontier. *)
              let new_var = gen_row_u (`G new_g) in
              cops.constrain_row row_var new_var;
              new_var
            else begin
              let ret = match row with
                | Extend(_, l, ty, rest) ->
                    UnionFind.make (Extend(new_var, l, go ty, go_row rest))
                | Empty _ ->
                    UnionFind.make (Empty new_var)
                | Row _ ->
                    UnionFind.make (Row new_var)
              in
              UnionFind.merge unify_row map_copy ret;
              ret
            end
      end
    in go old_root

let propagate: constraint_ops -> g_node -> u_type UnionFind.var -> unit =
  fun cops g var ->
    begin match (get_ty_bound (UnionFind.get var)).b_at with
      | `G g' ->
        let instance = expand cops g g' in
        cops.constrain_ty instance var
      | `Ty _ ->
          failwith "propagate: node not bound at g-node."
    end

(* TODO: why are we using a map to unit here, rather than a set? *)
let rec emit_all_nodes_ty: u_type UnionFind.var -> unit IntMap.t ref -> unit =
  fun v dict ->
    let t = UnionFind.get v in
    let {ty_id = n; ty_bound} = get_tyvar t in
    if Map.mem !dict n then
      ()
    else begin
      dict := Map.set !dict ~key:n ~data:();
      emit_bind_edge n ty_bound dict;
      begin match t with
        | Type _ ->
            Debug.show_node `TyVar n
        | Fn(_, param, ret) ->
            Debug.show_node `TyFn n;
            Debug.show_edge `Structural n ((get_tyvar (UnionFind.get param)).ty_id);
            Debug.show_edge `Structural n ((get_tyvar (UnionFind.get ret)).ty_id);
            emit_all_nodes_ty param dict;
            emit_all_nodes_ty ret dict
            (* TODO: bounding edges *)
        | Record (_, row) ->
            Debug.show_node `TyRecord n;
            Debug.show_edge `Structural n ((get_row_var (UnionFind.get row)).ty_id);
            emit_all_nodes_row row dict
        | Union (_, row) ->
            Debug.show_node `TyUnion n;
            Debug.show_edge `Structural n ((get_row_var (UnionFind.get row)).ty_id);
            emit_all_nodes_row row dict
      end
    end
and emit_all_nodes_row v dict =
    let r = UnionFind.get v in
    let {ty_id = n; ty_bound} = get_row_var r in
    if Map.mem !dict n then
      ()
    else begin
      dict := Map.set !dict ~key:n ~data:();
      emit_bind_edge n ty_bound dict;
      begin match r with
      | Empty _ ->
          Debug.show_node `RowEmpty n
      | Row _ ->
          Debug.show_node `RowVar n
      | Extend (_, lbl, h, t) ->
          Debug.show_node (`RowExtend lbl) n;
          Debug.show_edge `Structural n ((get_tyvar (UnionFind.get h)).ty_id);
          Debug.show_edge `Structural n ((get_row_var (UnionFind.get t)).ty_id);
          emit_all_nodes_ty h dict;
          emit_all_nodes_row t dict
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
    | Some (b_ty, g') ->
        Debug.show_edge (`Binding b_ty) g'.g_id g.g_id;
        emit_all_nodes_g g' dict
    | None ->
        ()
    end
  end
and emit_bind_edge n {b_at; b_ty} dict =
    match b_at with
    | `Ty parent ->
        emit_all_nodes_ty parent dict;
        let p_id = (get_tyvar (UnionFind.get parent)).ty_id in
        Debug.show_edge (`Binding b_ty) p_id n
    | `G g ->
        emit_all_nodes_g g dict;
        Debug.show_edge (`Binding b_ty) g.g_id n


let render_graph cs =
  if Config.render_constraints then
    let visited = ref (Map.empty (module Int)) in
    Debug.start_graph ();
    emit_all_nodes_ty cs.ty visited;
    List.iter cs.unification ~f:(function
      | UnifyTypes(l, r) ->
          let id n = (get_tyvar (UnionFind.get n)).ty_id in
          Debug.show_edge `Unify (id l) (id r);
          emit_all_nodes_ty l visited;
          emit_all_nodes_ty r visited
      | UnifyRows(l, r) ->
          let id n = (get_row_var (UnionFind.get n)).ty_id in
          Debug.show_edge `Unify (id l) (id r);
          emit_all_nodes_row l visited;
          emit_all_nodes_row r visited
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

let solve_constraints cs =
  let render_ucs = ref cs.unification in
  let render_ics = ref cs.instantiation in
  let render () = render_graph
    { unification = !render_ucs
    ; instantiation = !render_ics
    ; ty = cs.ty
    }
  in
  render ();
  let solve_unify vars =
    render_ucs := vars;
    List.iter vars ~f:(fun c ->
      begin match c with
      | UnifyTypes(l, r) -> UnionFind.merge unify l r
      | UnifyRows(l, r) -> UnionFind.merge unify_row l r
      end;
      render_ucs := List.tl_exn !render_ucs;
      render ();
    )
  in
  solve_unify cs.unification;
  top_sort_inst cs.instantiation
  |> List.iter ~f:(fun (g, ts) ->
      List.iter ts ~f:(fun t ->
        let cops, ucs, _ = make_cops () in
        propagate cops g t;
        solve_unify !ucs;
        render ()
      );
      render_ics := Map.remove !render_ics g.g_id;
    );
  cs.ty

let typecheck expr =
  try
    build_constraints expr
    |> solve_constraints
    |> get_var_type
    |> fun t -> Ok t
  with
    MuleErr.MuleExn e ->
      Err e
