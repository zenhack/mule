module S = Set.Make(String)
module Env = Map.Make(String)

open Gensym
open OrErr

(* The type of values associated with unification variables *)
type u_type =
  | Type of int
  | Fn of (int * u_type UnionFind.var * u_type UnionFind.var)
  | Record of (int * u_row UnionFind.var)
  | Union of (int * u_row UnionFind.var)
and u_row =
  | Extend of (Ast.label * u_type UnionFind.var * u_row UnionFind.var)
  | Empty
  | Row of int

let rec unify l r = OrErr.(
  match l, r with
  | (Fn (i, ll, lr), Fn (_, rl, rr)) ->
      UnionFind.merge unify ll rl
      >>= fun l' -> UnionFind.merge unify lr rr
      >>= fun r' -> Ok (Fn (i, l', r'))
  | (Record (i, row_l), Record(_, row_r)) ->
      UnionFind.merge unify_row row_l row_r
      |>> fun row_ret -> Record (i, row_ret)
  | (Type _, r) -> Ok r
  | (l, Type _) -> Ok l
  | (_, _) -> Err Error.TypeMismatch
)
and unify_row l r =
  match l, r with
  | (Empty, Empty) -> Ok Empty
  | (Extend (l_lbl, l_ty, l_rest), Extend (r_lbl, r_ty, r_rest)) ->
      if l_lbl = r_lbl then
        UnionFind.merge unify l_ty r_ty
        >>= fun ret_ty -> UnionFind.merge unify_row l_rest r_rest
        |>> fun ret_rest -> Extend (l_lbl, ret_ty, ret_rest)
      else
        UnionFind.merge unify_row
          r_rest
          (UnionFind.make (Extend(l_lbl, l_ty, UnionFind.make (Row (gensym())))))
        >>= fun _ ->
        UnionFind.merge unify_row
          l_rest
          (UnionFind.make (Extend(r_lbl, r_ty, UnionFind.make (Row (gensym())))))
        |>> fun rest ->
          Extend(l_lbl, l_ty, rest)

  | (Row _, r) -> Ok r
  | (l, Row _) -> Ok l
  | (Extend _, Empty) -> Err Error.TypeMismatch
  | (Empty, Extend _) -> Err Error.TypeMismatch

let decorate expr =
  Ast.Surface.Expr.map_info (fun _ -> UnionFind.make (Type (gensym ()))) expr

let rec walk env =
  let open Ast.Surface in
  function
  | Expr.Var (uVar, Ast.Var v) ->
      UnionFind.merge unify uVar (Env.find v env)
  | Expr.Lam (fVar, Ast.Var param, body) ->
      let paramVar = UnionFind.make (Type (gensym ())) in
      walk (Env.add param paramVar env) body
      >>= fun retVar ->
        UnionFind.merge unify
          fVar
          (UnionFind.make (Fn (gensym (), paramVar, retVar)))
  | Expr.App (retVar, f, arg) ->
      walk env f
      >>= fun fVar -> walk env arg
      >>= fun argVar ->
        UnionFind.merge unify
          fVar
          (UnionFind.make (Fn (gensym (), argVar, retVar)))
      >> Ok retVar
  | Expr.Record (retVar, fields) ->
      walk_fields env fields
      >>= fun rowVar -> UnionFind.merge unify
          retVar
          (UnionFind.make (Record (gensym (), rowVar)))
  | Expr.GetField (retVar, e, lbl) ->
      walk env e
      >>= fun tyvar ->
      let rowVar = UnionFind.make (Row (gensym ())) in
      let recVar = UnionFind.make (Record (gensym(), rowVar)) in
      UnionFind.merge unify
        recVar
        tyvar
      >>= fun _ ->
      let tailVar = UnionFind.make (Row (gensym ())) in
      UnionFind.merge unify_row
          rowVar
          (UnionFind.make (Extend(lbl, retVar, tailVar)))
      |>> fun _ -> retVar
  | Expr.Ctor (retVar, lbl) ->
      let paramVar = UnionFind.make (Type (gensym ())) in
      let rowVar = UnionFind.make
          (Extend
            ( lbl
            , paramVar
            , UnionFind.make (Row (gensym ()))
            )
          )
      in
      UnionFind.merge unify
        retVar
        (UnionFind.make
          (Fn
            ( gensym ()
            , paramVar
            , UnionFind.make (Union (gensym (), rowVar))
            )
          )
        )
and walk_fields env =
  function
  | [] -> Ok (UnionFind.make Empty)
  | ((lbl, ty) :: fs) ->
      walk env ty
      >>= fun lblVar -> walk_fields env fs
      |>> fun tailVar ->
        UnionFind.make (Extend(lbl, lblVar, tailVar))


let ivar i = "t" ^ string_of_int i

let maybe_add_rec i vars ty =
  let myvar = ivar i in
  if S.mem myvar vars then
    ( S.remove myvar vars
    , Ast.Surface.Type.Recur(i, Ast.Var myvar, ty)
    )
  else
    (vars, ty)

let rec add_rec_binders ty =
  let open Ast.Surface.Type in
  match ty with
  | Var (_, (Ast.Var v)) ->
      ( S.singleton v
      , ty
      )
  | Recur(i, v, t) ->
      let (vs, ts) = add_rec_binders t in
      ( S.remove (ivar i) vs
      , Recur(i, v, ts)
      )
  | Fn (i, f, x) ->
      let (fv, ft) = add_rec_binders f in
      let (xv, xt) = add_rec_binders x in
      maybe_add_rec i (S.union fv xv) (Fn(i, ft, xt))
  | Record(i, fields, rest) ->
      let (vars, ret) = row_add_rec_binders i fields rest in
      maybe_add_rec i vars (Record ret)
  | Union(i, ctors, rest) ->
      let (vars, ret) = row_add_rec_binders i ctors rest in
      maybe_add_rec i vars (Union ret)
and row_add_rec_binders i fields rest =
  let row_var = match rest with
    | Some (Ast.Var v) -> S.singleton v
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

let rec get_var_type env = function
  | Type i -> Ast.Surface.Type.Var (i, Ast.Var (ivar i))
  | Fn (i, f, x) ->
      if S.mem (ivar i) env then
        get_var_type env (Type i)
      else
        let env' = S.add (ivar i) env in
        Fn
          ( i
          , get_var_type env' (UnionFind.get f)
          , get_var_type env' (UnionFind.get x)
          )
  | Record (i, fields) ->
      let (fields, rest) =
        get_var_row (S.add (ivar i) env) (UnionFind.get fields)
      in
      Ast.Surface.Type.Record (i, fields, rest)
  | Union (i, ctors) ->
      let (ctors, rest) =
        get_var_row (S.add (ivar i) env) (UnionFind.get ctors)
      in
      Ast.Surface.Type.Union (i, ctors, rest)
and get_var_row env = function
  | Row i -> ([], Some (Ast.Var (ivar i)))
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

let typecheck expr =
  Lint.check_unbound expr
  >>= fun () -> Ok (decorate expr)
  >>= walk Env.empty
  |>> get_var_type
