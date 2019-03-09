module S = Set.Make(Ast.Var)
module Env = Map.Make(Ast.Var)

module IntMap = Map.Make(struct
  type t = int
  let compare = compare
end)
module IntSet = Set.Make(struct
  type t = int
  let compare = compare
end)

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
and bound_ty = Rigid | Flex
and bound = {
  b_ty: bound_ty;
  b_at: bound_target;
}
and tyvar = (int * bound)
and g_node = {
  g_id: int;
  g_bound: (bound_ty * g_node) option;
  g_child: u_type UnionFind.var Lazy.t;
}
and bound_target =
  [ `Ty of u_type UnionFind.var
  | `G of g_node
  ]

(* Helpers for signaling type errors *)
let typeErr e = raise (Error.MuleExn (Error.TypeError e))
let permErr op = typeErr (Error.PermissionErr op)
let ctorErr l r = typeErr (Error.MismatchedCtors (l, r))

type permission = F | R | L

let with_g
  : ((bound_ty * g_node) option)
  -> (g_node Lazy.t -> (u_type UnionFind.var * 'a))
  -> (g_node * u_type UnionFind.var * 'a)
  = fun parent f ->
      let gid = gensym () in
      let rec g = lazy {
        g_id = gid;
        g_bound = parent;
        g_child = lazy (fst (Lazy.force ret));
      }
      and ret = lazy (f g)
      in (Lazy.force g, fst (Lazy.force ret), snd (Lazy.force ret))

(* Get the "permission" of a node, based on the node's binding path
 * (starting from the node and working up the tree). See section 3.1
 * in {MLF-Graph-Unify}. *)
let rec get_permission: bound_ty list -> permission = function
  | [] -> F
  | (Rigid :: _) -> R
  | (Flex :: bs) ->
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
  fun ty -> snd (get_tyvar ty)
let get_row_var: u_row -> tyvar = function
  | Extend(v, _, _, _) -> v
  | Empty v -> v
  | Row v -> v
let get_row_bound: u_row -> bound =
  fun r -> snd (get_row_var r)

let rec show_u_type_v s v =
  let t = UnionFind.get v in
  let (n, _) = get_tyvar t in
  if IntSet.mem n s then
    "t" ^ string_of_int n
  else
    let s = IntSet.add n s in
    match t with
    | Type _ -> "t" ^ string_of_int n
    | Fn (_, l, r) ->
        "(" ^ show_u_type_v s l ^ " -> " ^ show_u_type_v s r ^ ")"
    | Record(_, row) ->
        "Record{" ^ show_u_row_v s row ^ "}"
    | Union(_, row) ->
        "Union(" ^ show_u_row_v s row ^ ")"
and show_u_row_v s v =
  let r = UnionFind.get v in
  let (n, _) = get_row_var r in
  if IntSet.mem n s then
    "r" ^ string_of_int n
  else
    let s = IntSet.add n s in
    match r with
    | Row (n, _) ->
        "r" ^ string_of_int n
    | Empty _ ->
        "<empty>"
    | Extend (_, lbl, ty, rest) ->
        "(" ^ Ast.Label.to_string lbl ^ " => " ^ show_u_type_v s ty ^ ") :: " ^ show_u_row_v s rest
let show_u_type_v = show_u_type_v IntSet.empty
let show_u_row_v  = show_u_row_v  IntSet.empty

let show_g {g_child; _} =
  show_u_type_v (Lazy.force g_child)


let bound_target_id: bound_target -> int = function
  | `Ty tv ->
      fst (get_tyvar (UnionFind.get tv))
  | `G g ->
      g.g_id

let bound_id: bound -> int =
  fun b -> bound_target_id b.b_at

let older_bound: bound_target -> bound -> bool =
  fun targ bound ->
    bound_target_id targ < bound_id bound

let rec tyvar_bound_list: tyvar -> bound_ty list =
  fun (_, bound) ->
    let {b_ty; b_at} = bound in
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
  (gensym (), {
    b_ty = Flex;
    b_at = `G g;
  })


let gen_ty_u: bound_target -> u_type UnionFind.var = fun targ ->
  UnionFind.make (Type (gensym(), {b_ty = Flex; b_at = targ}))
let gen_row_u: bound_target -> u_row UnionFind.var = fun targ ->
  UnionFind.make (Row (gensym(), {b_ty = Flex; b_at = targ}))

let gen_ty_u_g g =
  UnionFind.make (Type (gen_ty_var g))


let b_at_id = function
  | `G {g_id; _} -> g_id
  | `Ty u -> fst (get_tyvar (UnionFind.get u))

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
      Some (snd (get_tyvar (UnionFind.get u)))

let raised_bound b = match b with
  | {b_ty = Rigid; _} ->
      permErr `Raise
  | _ ->
      bound_next b

(* Compute the lease common ancestor of two bounds.
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

(* "Unify" to bounding edges. This does a combination of raising and
 * weakening as needed to make them the same. *)
let unify_bound l r =
  let {b_at; _} = bound_lca l r in
  match l.b_ty, r.b_ty with
  | Flex, Flex -> {b_at; b_ty = Flex}
  | _ -> {b_at; b_ty = Rigid}

let unify_tyvar: tyvar -> tyvar -> tyvar =
 fun (i, bl) (_, br) ->
  (i, unify_bound bl br)

let rec unify l r =
  let tv = unify_tyvar (get_tyvar l) (get_tyvar r) in
  match l, r with
  | Type (lv, _), Type (rv, _) when lv = rv ->
      (* same type variable; just return it *)
      l

  | ((Type _) as v), t | t, ((Type _) as v) ->
      (* Corresponds to "grafting" in {MLF-Graph-Unify}. Only valid for flexible
       * bottom vars. *)
      begin match ty_permission v with
        | F -> t
        | _ -> permErr `Graft
      end

  | _ when tyvar_permission tv = L ->
      (* We need to do a merge, but our permissions are locked;
       * fail. *)
      permErr `Merge

  (* Top level type constructor that matches. In the
   * literature, these are treated uniformly and opaquely.
   * We have a case for each just because (a) we have a
   * so few of them them, and (b) we have to deal with
   * different kinds of argument variables. In principle we
   * could factor out the commonalities, and maybe we will
   * eventually, but for now there just isn't that much. *)
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

  (* Type constructor mismatches. we could have a catchall,
   * but this means we don't forget a case, and we can produce
   * better error messages. it would be nice to refactor so
   * we don't have to list every combination though. *)
  | Fn     _, Record _ -> ctorErr `Fn     `Record
  | Fn     _, Union  _ -> ctorErr `Fn     `Union
  | Record _, Fn     _ -> ctorErr `Record `Fn
  | Record _, Union  _ -> ctorErr `Record `Union
  | Union  _,  Fn    _ -> ctorErr `Union  `Fn
  | Union  _, Record _ -> ctorErr `Union  `Record
and unify_row l r =
  let tv = unify_tyvar (get_row_var l) (get_row_var r) in
  match l, r with
  | (Empty _, Empty _) -> Empty tv
  | (Extend (_, l_lbl, l_ty, l_rest), Extend (_, r_lbl, r_ty, r_rest)) ->
      let ret = Extend (tv, l_lbl, l_ty, l_rest) in
      if l_lbl = r_lbl then begin
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
          UnionFind.make (Row (gensym (), get_row_bound (UnionFind.get v)))
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
      (* FIXME: we need to make sure to make an instance edge if the variable refers
       * to something that can be instatiated. This probably means changing env to
       * allow carrying g-nodes or something.
       *
       * I(@zenhack) also suspect we may be misplacing some g-nodes; need to audit.
       *)
      begin match Env.find v env with
        | `Ty tv -> tv
        | `G g' ->
            let tv = gen_ty_u_g g in
            cops.constrain_inst g' tv;
            tv
      end
  | Expr.Lam (param, body) ->
      let (g', ty, fVar) = with_g (Some (Flex, g)) begin fun g ->
          let fVar = gen_ty_u_g (Lazy.force g) in
          let paramVar = gen_ty_u_g (Lazy.force g) in
          let retVar = walk cops (Env.add param (`Ty paramVar) env) (Lazy.force g) body in
          ( UnionFind.make (Fn (get_tyvar (UnionFind.get fVar), paramVar, retVar))
          , fVar
          )
        end
      in
      cops.constrain_inst g' fVar;
      ty
  | Expr.Let(v, e, body) ->
      let (gE, _eVar, ()) = with_g
        (Some(Flex, g))
        (fun g -> walk cops env (Lazy.force g) e, ())
      in
      (* cops.constrain_inst gE eVar; *)
      let (_gBody, bodyVar, ()) = with_g
        (Some(Flex, g))
        (fun g ->
          ( walk cops (Env.add v (`G gE) env) (Lazy.force g) body
          , ()
          ))
      in
      (* cops.constrain_inst gBody bodyVar; *)
      bodyVar
  | Expr.App (f, arg) ->
      let (gF, fVar, ()) = with_g
        (Some(Flex, g))
        (fun g -> walk cops env (Lazy.force g) f, ())
      in
      cops.constrain_inst gF fVar;
      let (gArg, argVar, ()) = with_g
        (Some(Flex, g))
        (fun g -> (walk cops env (Lazy.force g) arg, ()))
      in
      cops.constrain_inst gArg argVar;
      let retVar = gen_ty_u_g g in
      cops.constrain_ty
        fVar
        (UnionFind.make (Fn (gen_ty_var g, argVar, retVar)));
      retVar
  | Expr.Record fields ->
      let rVar = gen_ty_var g in
      let tailVar = UnionFind.make (Empty (gen_ty_var g)) in
      let row = walk_fields cops env g tailVar (RowMap.bindings fields) in
      UnionFind.make (Record (rVar, row))
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
  | Expr.Update (r, updates) ->
      let retTyV = gen_ty_var g in
      let origVar = walk cops env g r in
      let tailVar = UnionFind.make (Row (gen_ty_var g)) in
      let updateVar = walk_fields cops env g tailVar updates in
      cops.constrain_ty
          origVar
          (UnionFind.make (Record (gen_ty_var g, tailVar)));
      UnionFind.make (Record (retTyV, updateVar))
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
  | Expr.Match {cases; default} when RowMap.is_empty cases ->
      begin match default with
        | None -> raise (Error.MuleExn EmptyMatch)
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
      let (rowVar, bodyVar) = walk_match cops env g final (RowMap.bindings cases) in
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
      let bodyVar = walk cops (Env.add var (`Ty ty) env) g body in
      let (row, body') = walk_match cops env g final rest in
      cops.constrain_ty bodyVar body';
      ( UnionFind.make (Extend(gen_ty_var g, lbl, ty, row))
      , bodyVar
      )
and walk_fields cops env g final = function
  | [] -> final
  | ((lbl, ty) :: fs) ->
      let lblVar = walk cops env g ty in
      let tailVar = walk_fields cops env g final fs in
      UnionFind.make (Extend(gen_ty_var g, lbl, lblVar, tailVar))

let ivar i = Ast.Var.of_string ("t" ^ string_of_int i)

let maybe_add_rec i vars ty =
  let myvar = ivar i in
  if S.mem myvar vars then
    ( S.remove myvar vars
    , Type.Recur(i, myvar, ty)
    )
  else
    (vars, ty)

let rec add_rec_binders ty =
  match ty with
  | Type.Var (_, v) ->
      ( S.singleton v
      , ty
      )
  | Type.Recur(i, v, t) ->
      let (vs, ts) = add_rec_binders t in
      ( S.remove (ivar i) vs
      , Type.Recur(i, v, ts)
      )
  | Type.Fn (i, f, x) ->
      let (fv, ft) = add_rec_binders f in
      let (xv, xt) = add_rec_binders x in
      maybe_add_rec i (S.union fv xv) (Type.Fn(i, ft, xt))
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
    | Some v -> S.singleton v
    | None -> S.empty
  in
  let fields_vars = List.map
    (fun (lbl, ty) -> (lbl, add_rec_binders ty))
    fields
  in
  let vars = List.fold_left
    (fun accum (_, (vars, _)) -> S.union accum vars)
    row_var
    fields_vars
  in
  let fields' = List.map (fun (lbl, (_, ty)) -> (lbl, ty)) fields_vars in
  (vars, (i, fields', rest))
let add_rec_binders ty =
  snd (add_rec_binders ty)

(* Extract a type from a (solved) unification variable. *)
let rec get_var_type env = function
  | Type (i, _) -> Type.Var (i, (ivar i))
  | Fn ((i, b), f, x) ->
      if S.mem (ivar i) env then
        get_var_type env (Type (i, b))
      else
        let env' = S.add (ivar i) env in
        Fn
          ( i
          , get_var_type env' (UnionFind.get f)
          , get_var_type env' (UnionFind.get x)
          )
  | Record ((i, _), fields) ->
      let (fields, rest) =
        get_var_row (S.add (ivar i) env) (UnionFind.get fields)
      in
      Type.Record (i, fields, rest)
  | Union ((i, _), ctors) ->
      let (ctors, rest) =
        get_var_row (S.add (ivar i) env) (UnionFind.get ctors)
      in
      Type.Union (i, ctors, rest)
and get_var_row env = function
  | Row (i, _) -> ([], Some (ivar i))
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
    |> get_var_type S.empty
    |> add_rec_binders

type unify_edge =
  | UnifyTypes of (u_type UnionFind.var * u_type UnionFind.var)
  | UnifyRows of (u_row UnionFind.var * u_row UnionFind.var)

type built_constraints =
  { unification: unify_edge list
  ; instatiation: (g_node * (u_type UnionFind.var) list) IntMap.t
  ; ty: u_type UnionFind.var
  }

let make_cops: unit ->
  ( constraint_ops
  * (unify_edge list) ref
  * ((g_node * (u_type UnionFind.var) list) IntMap.t) ref
  ) = fun () ->
  let report =
    if Config.dump_constraints then
      fun f -> print_endline (f ())
    else
      fun _ -> ()
  in
  let ucs = ref [] in (* unification constraints *)
  let ics = ref IntMap.empty in (* instantiation constraints *)
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
          ics := begin IntMap.update g.g_id
            begin function
              | None -> Some (g, [t])
              | Some (_, ts) -> Some (g, (t :: ts))
            end
            !ics
          end
        end
    }
  in (cops, ucs, ics)

let build_constraints: Expr.t -> built_constraints = fun expr ->
  let cops, ucs, ics = make_cops () in
  let (_, ty, ()) =
    with_g None begin fun g ->
      (walk cops Env.empty (Lazy.force g) expr, ())
    end
  in
  { unification = !ucs
  ; instatiation = !ics
  ; ty = ty
  }

(* Expand an instatiation constraint rooted at a g_node. See
 * section 3.1 of {MLF-Graph-Infer}.
 *)
let expand: constraint_ops -> g_node -> bound_target -> u_type UnionFind.var =
  fun cops old_g new_targ ->
    let old_root = Lazy.force old_g.g_child in

    (* Generate the unification variable for the root up front, so it's
     * visible everywhere. *)
    let new_root_tv = (gensym (), {
      b_ty = Flex;
      b_at = new_targ;
    }) in
    let new_root = gen_ty_u new_targ in

    let rec go = fun nv ->
      let n = UnionFind.get nv in
      let old_bound = get_ty_bound n in
      if not (older_bound (`G old_g) old_bound) then
        (* We've hit the frontier; replace it with a bottom node and
         * constrain it to be equal to the old thing. *)
        let new_var = gen_ty_u new_targ in
        cops.constrain_ty nv new_var;
        new_var
      else
        (* First, generate the new bound. *)
        let new_tyvar =
          if nv = old_root then
            new_root_tv
          else
            ( gensym ()
            , { b_ty = old_bound.b_ty
              ; b_at = `Ty new_root
              }
            )
        in
        (* Now do a deep copy, subbing in the new bound. *)
        let ret = UnionFind.make (match n with
          | Type _ -> Type new_tyvar
          | Fn (_, param, ret) -> Fn(new_tyvar, go param, go ret)
          | Record(_, row) -> Record(new_tyvar, go_row row)
          | Union(_, row) -> Union(new_tyvar, go_row row))
        in
        if nv = old_root then
          (* If we were the root we have to unify with the variable created above;
           * we couldn't set this at the top because of the cyclic dependency.
           *)
          begin
            UnionFind.merge unify new_root ret;
            ret
          end
        else
          ret

    and go_row row_var =
      let row = UnionFind.get row_var in
      let old_bound = get_row_bound row in
      let new_var = (gensym (), {
        b_ty = old_bound.b_ty;
        b_at = `Ty new_root
      })
      in
      if not (older_bound (`G old_g) old_bound) then
        (* On the frontier. *)
        let new_var = gen_row_u new_targ in
        cops.constrain_row row_var new_var;
        new_var
      else
        match row with
          | Extend(_, l, ty, rest) ->
              UnionFind.make (Extend(new_var, l, go ty, go_row rest))
          | Empty _ ->
              UnionFind.make (Empty new_var)
          | Row _ ->
              UnionFind.make (Row new_var)
    in go old_root

let propogate: constraint_ops -> g_node -> u_type UnionFind.var -> unit =
  fun cops g var ->
    let instance = expand
      cops
      g
      (get_ty_bound (UnionFind.get var)).b_at
    in
    cops.constrain_ty instance var

let solve_constraints cs =
  let solve_unify vars =
    List.iter (function
      | UnifyTypes(l, r) -> UnionFind.merge unify l r
      | UnifyRows(l, r) -> UnionFind.merge unify_row l r
    ) vars
  in
  solve_unify cs.unification;
  IntMap.bindings cs.instatiation
  |> List.sort (fun (l, _) (r, _) -> compare r l)
  |> List.iter
    (fun (_, (g, ts)) ->
      List.iter
        (fun t ->
          let cops, ucs, _ = make_cops () in
          propogate cops g t;
          solve_unify !ucs
        )
        ts
    );
  cs.ty

let typecheck expr =
  try
    build_constraints expr
    |> solve_constraints
    |> get_var_type
    |> fun t -> Ok t
  with
    Error.MuleExn e ->
      Err e
