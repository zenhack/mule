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
and bound_ty = (* Rigid | *) Flex
and bound = {
  b_ty: bound_ty;
  b_at: g_node;
}
and tyvar = (int * bound ref)
and g_node = {
  g_bound: g_node option;
  g_child: u_type UnionFind.var Lazy.t;
}

let gen_ty_var g =
  (gensym (), ref {
    b_ty = Flex;
    b_at = Lazy.force g;
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
      let l' = UnionFind.merge unify ll rl in
      let r' = UnionFind.merge unify lr rr in
      Fn (i, l', r')
  | (Record (i, row_l), Record(_, row_r)) ->
      let row_ret = UnionFind.merge unify_row row_l row_r in
      Record (i, row_ret)
  | (Union (i, row_l), Union(_, row_r)) ->
      let row_ret = UnionFind.merge unify_row row_l row_r in
      Union(i, row_ret)

  (* Type constructor mismatches. we could have a catchall,
   * but this means we don't forget a case. it would be nice
   * to refactor so we don't have to list every combination
   * though. *)
  | Fn _, Record _ | Fn _, Union _
  | Record _, Fn _ | Record _, Union _
  | Union _, Fn _ | Union _, Record _ ->
      raise (Error.MuleExn Error.TypeMismatch)

  | Type _, t | t, Type _ -> t
and unify_row l r =
  match l, r with
  | (Empty, Empty) -> Empty
  | (Extend (l_lbl, l_ty, l_rest), Extend (r_lbl, r_ty, r_rest)) ->
      if l_lbl = r_lbl then
        let ret_ty = UnionFind.merge unify l_ty r_ty in
        let ret_rest = UnionFind.merge unify_row l_rest r_rest in
        Extend (l_lbl, ret_ty, ret_rest)
      else
        let _ = UnionFind.merge unify_row
          r_rest
          (UnionFind.make (Extend(l_lbl, l_ty, UnionFind.make (Row (gensym())))))
        in
        let rest = UnionFind.merge unify_row
          l_rest
          (UnionFind.make (Extend(r_lbl, r_ty, UnionFind.make (Row (gensym())))))
        in
        Extend(l_lbl, l_ty, rest)

  | (Row _, r) -> r
  | (l, Row _) -> l
  | (Extend _, Empty) -> raise (Error.MuleExn Error.TypeMismatch)
  | (Empty, Extend _) -> raise (Error.MuleExn Error.TypeMismatch)

let rec walk env g = function
  | Expr.Var v ->
      Env.find v env
  | Expr.Lam (param, body) ->
      let paramVar = gen_ty_u g in
      let retVar = walk (Env.add param paramVar env) g body in
      UnionFind.make (Fn (gen_ty_var g, paramVar, retVar))
  | Expr.App (f, arg) ->
      let fVar = walk env g f in
      let argVar = walk env g arg in
      let retVar = gen_ty_u g in
      let _ = UnionFind.merge unify
        fVar
        (UnionFind.make (Fn (gen_ty_var g, argVar, retVar)))
      in
      retVar
  | Expr.Record fields ->
      let row = walk_fields env g (UnionFind.make Empty) (RowMap.bindings fields) in
      UnionFind.make (Record (gen_ty_var g, row))
  | Expr.GetField (e, lbl) ->
      let tyvar = walk env g e in
      let rowVar = UnionFind.make (Row (gensym ())) in
      let recVar = UnionFind.make (Record (gen_ty_var g, rowVar)) in
      let _ = UnionFind.merge unify
        recVar
        tyvar
      in
      let tailVar = UnionFind.make (Row (gensym ())) in
      let fieldVar = gen_ty_u g in
      let _ = UnionFind.merge unify_row
        rowVar
        (UnionFind.make (Extend(lbl, fieldVar, tailVar)))
      in
      fieldVar
  | Expr.Update (r, updates) ->
      let origVar = walk env g r in
      let tailVar = UnionFind.make (Row (gensym())) in
      let updateVar = walk_fields env g tailVar updates in
      let _ = UnionFind.merge unify
          origVar
          (UnionFind.make (Record (gen_ty_var g, tailVar)))
      in
      UnionFind.make (Record (gen_ty_var g, updateVar))
  | Expr.Ctor (lbl, param) ->
      let paramVar = walk env g param in
      UnionFind.make
        ( Union
          ( gen_ty_var g
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
            walk env g (Expr.Lam (paramVar, body))
        | Some (None, body) ->
            walk env g (Expr.Lam (Ast.Var.of_string "_", body))
      end
  | Expr.Match {cases; default} ->
      let final = match default with
        | None -> UnionFind.make Empty
        | Some _ -> UnionFind.make (Row (gensym ()))
      in
      let (rowVar, bodyVar) = walk_match env g final (RowMap.bindings cases) in
      UnionFind.make
        ( Fn
            ( gen_ty_var g
            , UnionFind.make (Union(gen_ty_var g, rowVar))
            , bodyVar
            )
        )
and walk_match env g final = function
  | [] -> (final, gen_ty_u g)
  | ((lbl, (var, body)) :: rest) ->
      let ty = gen_ty_u g in
      let bodyVar = walk (Env.add var ty env) g body in
      let (row, body') = walk_match env g final rest in
      let bvar = UnionFind.merge unify bodyVar body' in
      ( UnionFind.make (Extend(lbl, ty, row))
      , bvar
      )
and walk_fields env g final = function
  | [] -> final
  | ((lbl, ty) :: fs) ->
      let lblVar = walk env g ty in
      let tailVar = walk_fields env g final fs in
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

let with_g
  : (g_node option)
  -> (g_node Lazy.t -> (u_type UnionFind.var * 'a))
  -> (g_node * u_type UnionFind.var * 'a)
  = fun parent f ->
      let rec g = lazy {
        g_bound = parent;
        g_child = lazy (fst (Lazy.force ret));
      }
      and ret = lazy (f g)
      in (Lazy.force g, fst (Lazy.force ret), snd (Lazy.force ret))

let typecheck expr =
  try
    let (_, _, ret) =
      with_g None begin fun g ->
        let ty = walk Env.empty g expr in
        ( ty
        , (Ok (get_var_type ty))
        )
      end
    in ret
  with
    Error.MuleExn e ->
      Err e
