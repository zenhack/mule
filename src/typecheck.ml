module S = Set.Make(Ast.Var)
module Env = Map.Make(Ast.Var)

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
  | Extend of (Ast.Label.t * u_type UnionFind.var * u_row UnionFind.var)
  | Empty
  | Row of int
and bound_ty = Rigid | Flex
and bound = {
  b_ty: bound_ty;
  b_at:
    [ `Ty of u_type UnionFind.var
    | `G of g_node
    ];
}
and tyvar = (int * bound ref)
and g_node = {
  g_id: int;
  g_bound: (bound_ty * g_node) option;
  g_child: u_type UnionFind.var Lazy.t;
}

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
 * in {MLF-Graph}. *)
let rec get_permission: bound_ty list -> permission = function
  | [] -> F
  | (Rigid :: _) -> R
  | (Flex :: bs) ->
      begin match get_permission bs with
        | F -> F
        | R -> L
        | L -> L
      end

let rec gnode_bound_list {g_bound; _} = match g_bound with
  | None -> []
  | Some (b_ty, g) -> b_ty :: gnode_bound_list g
let get_tyvar = function
  | Type v -> v
  | Fn (v, _, _) -> v
  | Record (v, _) -> v
  | Union (v, _) -> v

let rec tyvar_bound_list: tyvar -> bound_ty list =
  fun (_, bound) ->
    let {b_ty; b_at} = !bound in
    match b_at with
    | `G g -> b_ty :: gnode_bound_list g
    | `Ty t -> b_ty :: ty_bound_list (UnionFind.get t)
and ty_bound_list ty =
tyvar_bound_list (get_tyvar ty)

let ty_permission: u_type -> permission =
  fun ty ->
    get_permission (ty_bound_list ty)

type constraint_ops =
  { constrain_ty   : u_type UnionFind.var -> u_type UnionFind.var -> unit
  ; constrain_row  : u_row UnionFind.var  -> u_row UnionFind.var  -> unit
  ; constrain_inst : g_node -> u_type UnionFind.var -> unit
  }

let gen_ty_var g =
  (gensym (), ref {
    b_ty = Flex;
    b_at = `G g;
  })

let gen_ty_u g =
  UnionFind.make (Type (gen_ty_var g))

let rec unify l r =
  match l, r with
  (* same type variable. *)
  | Type (lv, _), Type (rv, rb) when lv = rv ->
      Type (rv, rb)

  (* Top level type constructor that matches. In the
   * literature, these are treated uniformly and opaquely.
   * We have a case for each just because (a) we have a
   * so few of them them, and (b) we have to deal with
   * different kinds of argument variables. In principle we
   * could factor out the commonalities, and maybe we will
   * eventually, but for now there just isn't that much. *)
  | (Fn (i, ll, lr), Fn (_, rl, rr)) ->
      UnionFind.merge unify ll rl;
      UnionFind.merge unify lr rr;
      Fn (i, ll, lr)
  | (Record (i, row_l), Record(_, row_r)) ->
      UnionFind.merge unify_row row_l row_r;
      Record (i, row_l)
  | (Union (i, row_l), Union(_, row_r)) ->
      UnionFind.merge unify_row row_l row_r;
      Union(i, row_l)

  (* Type constructor mismatches. we could have a catchall,
   * but this means we don't forget a case. it would be nice
   * to refactor so we don't have to list every combination
   * though. *)
  | Fn _, Record _ | Fn _, Union _
  | Record _, Fn _ | Record _, Union _
  | Union _, Fn _ | Union _, Record _ ->
      raise (Error.MuleExn Error.TypeMismatch)

  | ((Type _) as v), t | t, ((Type _) as v) ->
      (* Corresponds to "grafting" in {MLF-Graph}. Only valid for flexible
       * bottom vars. *)
      begin match ty_permission v with
        | F -> t
        | _ -> raise (Error.MuleExn Error.TypeMismatch)
      end
and unify_row l r =
  match l, r with
  | (Empty, Empty) -> Empty
  | (Extend (l_lbl, l_ty, l_rest), Extend (r_lbl, r_ty, r_rest)) ->
      if l_lbl = r_lbl then begin
        UnionFind.merge unify l_ty r_ty;
        UnionFind.merge unify_row l_rest r_rest;
        Extend (l_lbl, l_ty, l_rest)
      end else begin
        UnionFind.merge unify_row
          r_rest
          (UnionFind.make (Extend(l_lbl, l_ty, UnionFind.make (Row (gensym())))));
        UnionFind.merge unify_row
          l_rest
          (UnionFind.make (Extend(r_lbl, r_ty, UnionFind.make (Row (gensym())))));
        Extend(l_lbl, l_ty, l_rest)
      end

  | (Row _, r) -> r
  | (l, Row _) -> l
  | (Extend _, Empty) -> raise (Error.MuleExn Error.TypeMismatch)
  | (Empty, Extend _) -> raise (Error.MuleExn Error.TypeMismatch)

let rec walk cops env g = function
  | Expr.Var v ->
      Env.find v env
  | Expr.Lam (param, body) ->
      let (g', ty, retVar) = with_g (Some (Flex, g)) begin fun g ->
          let fVar = (gen_ty_var (Lazy.force g)) in
          let paramVar = gen_ty_u (Lazy.force g) in
          let retVar = walk cops (Env.add param paramVar env) (Lazy.force g) body in
          ( UnionFind.make (Fn (fVar, paramVar, retVar))
          , retVar
          )
        end
      in
      cops.constrain_inst g' retVar;
      ty
  | Expr.Let(v, e, body) ->
      let (gE, eVar, ()) = with_g
        (Some(Flex, g))
        (fun g -> walk cops env (Lazy.force g) e, ())
      in
      cops.constrain_inst gE eVar;
      let (gBody, bodyVar, ()) = with_g
        (Some(Flex, g))
        (fun g ->
          ( walk cops (Env.add v eVar env) (Lazy.force g) body
          , ()
          ))
      in
      cops.constrain_inst gBody bodyVar;
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
      let retVar = gen_ty_u g in
      cops.constrain_ty
        fVar
        (UnionFind.make (Fn (gen_ty_var g, argVar, retVar)));
      retVar
  | Expr.Record fields ->
      let rVar = gen_ty_var g in
      let row = walk_fields cops env g (UnionFind.make Empty) (RowMap.bindings fields) in
      UnionFind.make (Record (rVar, row))
  | Expr.GetField (e, lbl) ->
      let tyvar = walk cops env g e in
      let rowVar = UnionFind.make (Row (gensym ())) in
      let recVar = UnionFind.make (Record (gen_ty_var g, rowVar)) in
      cops.constrain_ty recVar tyvar;
      let tailVar = UnionFind.make (Row (gensym ())) in
      let fieldVar = gen_ty_u g in
      cops.constrain_row
        rowVar
        (UnionFind.make (Extend(lbl, fieldVar, tailVar)));
      fieldVar
  | Expr.Update (r, updates) ->
      let retTyV = gen_ty_var g in
      let origVar = walk cops env g r in
      let tailVar = UnionFind.make (Row (gensym())) in
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
                ( lbl
                , paramVar
                , UnionFind.make (Row (gensym ()))
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
        | None -> UnionFind.make Empty
        | Some _ -> UnionFind.make (Row (gensym ()))
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
  | [] -> (final, gen_ty_u g)
  | ((lbl, (var, body)) :: rest) ->
      let ty = gen_ty_u g in
      let bodyVar = walk cops (Env.add var ty env) g body in
      let (row, body') = walk_match cops env g final rest in
      cops.constrain_ty bodyVar body';
      ( UnionFind.make (Extend(lbl, ty, row))
      , bodyVar
      )
and walk_fields cops env g final = function
  | [] -> final
  | ((lbl, ty) :: fs) ->
      let lblVar = walk cops env g ty in
      let tailVar = walk_fields cops env g final fs in
      UnionFind.make (Extend(lbl, lblVar, tailVar))

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
  | Row i -> ([], Some (ivar i))
  | Empty -> ([], None)
  | Extend (lbl, ty, rest) ->
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

let build_constraints expr =
  let ucs = ref [] in (* unification constraints *)
  let cops =
    { constrain_ty   = (fun l r -> ucs := UnifyTypes(l, r) :: !ucs)
    ; constrain_row  = (fun l r -> ucs := UnifyRows(l, r) :: !ucs)
    ; constrain_inst = (fun _ _ -> ())
    }
  in
  let (_, ty, ()) =
    with_g None begin fun g ->
      (walk cops Env.empty (Lazy.force g) expr, ())
    end
  in
  (!ucs, ty)

let typecheck expr =
  (* TODO: this is here to squelch warnings about not using these, which we
   * will do in the future; at which point we should remove this: *)
  let _ = Rigid in

  let (constraints, ty) = build_constraints expr in
  try
    List.iter (function
      | UnifyTypes(l, r) -> UnionFind.merge unify l r
      | UnifyRows(l, r) -> UnionFind.merge unify_row l r
    ) constraints;
    Ok (get_var_type ty)
  with
    Error.MuleExn e ->
      Err e
