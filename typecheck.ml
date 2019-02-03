include Typecheck_t

module S = Set.Make(String)
module Env = Map.Make(String)

(* Free variables in a value-level expression *)
let rec expr_free_vars env = Ast.Expr.(
  function
  | Var (_, Ast.Var v) ->
      if S.mem v env then
        S.empty
      else
        S.singleton v
  | Lam (_, Ast.Var v, body) ->
      expr_free_vars (S.add v env) body
  | App (_, f, x) ->
      S.union (expr_free_vars env f) (expr_free_vars env x)
  | Record (_, fields) ->
      fields
        |> List.map (fun (_, v) -> expr_free_vars env v)
        |> List.fold_left S.union S.empty
  | GetField(_, e, _) ->
      expr_free_vars env e
)

(* Check for unbound variables. *)
let check_unbound expr =
  let free = expr_free_vars S.empty expr in
  match S.find_first_opt (fun _ -> true) free with
  | Some x -> OrErr.Err (UnboundVar (Ast.Var x))
  | None -> OrErr.Ok ()

(* The type of values associated with unification variables *)
type u_type =
  | Type of int
  | Fn of (int * u_type UnionFind.var * u_type UnionFind.var)
  | Record of (int * u_row UnionFind.var)
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
  | (_, _) -> Err Mismatch
)
and unify_row l r = OrErr.(
  match l, r with
  | (Empty, Empty) -> Ok Empty
  | (Extend (l_lbl, l_ty, l_rest), Extend (r_lbl, r_ty, r_rest)) ->
      if l_lbl = r_lbl then
        UnionFind.merge unify l_ty r_ty
        >>= fun ret_ty -> UnionFind.merge unify_row l_rest r_rest
        |>> fun ret_rest -> Extend (l_lbl, ret_ty, ret_rest)
      else
        Debug.todo "unify disparate labels"
  | (_, _) -> Err Mismatch
)

let decorate expr =
  Ast.Expr.map_info (fun _ -> UnionFind.make (Type (Gensym.gensym ()))) expr

let rec walk env = Ast.(OrErr.(
  function
  | Expr.Var (uVar, Ast.Var v) ->
      UnionFind.merge unify uVar (Env.find v env)
  | Expr.Lam (fVar, Ast.Var param, body) ->
      let paramVar = UnionFind.make (Type (Gensym.gensym ())) in
      walk (Env.add param paramVar env) body
      >>= fun retVar ->
        UnionFind.merge unify
          fVar
          (UnionFind.make (Fn (Gensym.gensym (), paramVar, retVar)))
  | Expr.App (retVar, f, arg) ->
      walk env f
      >>= fun fVar -> walk env arg
      >>= fun argVar ->
        UnionFind.merge unify
          fVar
          (UnionFind.make (Fn (Gensym.gensym (), argVar, retVar)))
      >> Ok retVar
  | Expr.Record (retVar, fields) ->
      walk_fields env fields
      >>= fun rowVar -> UnionFind.merge unify
          retVar
          (UnionFind.make (Record (Gensym.gensym (), rowVar)))
  | Expr.GetField (retVar, e, lbl) ->
      walk env e
      >>= fun tyvar ->
      let rowVar = UnionFind.make (Row (Gensym.gensym ())) in
      let recVar = UnionFind.make (Record (Gensym.gensym(), rowVar)) in
      UnionFind.merge unify
        recVar
        tyvar
      >>= fun _ ->
      let tailVar = UnionFind.make (Row (Gensym.gensym ())) in
      UnionFind.merge unify_row
          rowVar
          (UnionFind.make (Extend(lbl, retVar, tailVar)))
      |>> fun _ -> retVar
))
and walk_fields env = OrErr.(
  function
  | [] -> Ok (UnionFind.make Empty)
  | ((lbl, ty) :: fs) ->
      walk env ty
      >>= fun lblVar -> walk_fields env fs
      |>> fun tailVar ->
        UnionFind.make (Extend(lbl, lblVar, tailVar))
)


let ivar i = "t" ^ string_of_int i

let maybe_add_rec i vars ty =
  let myvar = ivar i in
  if S.mem myvar vars then
    ( S.remove myvar vars
    , Ast.Type.Recur(i, Ast.Var myvar, ty)
    )
  else
    (vars, ty)

let rec add_rec_binders ty = Ast.Type.(
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
      maybe_add_rec i vars (Record(i, fields', rest))
)
let add_rec_binders ty =
  snd (add_rec_binders ty)

let rec get_var_type env = function
  | Type i -> Ast.Type.Var (i, Ast.Var (ivar i))
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
      Ast.Type.Record (i, fields, rest)
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

let typecheck expr = OrErr.(
  check_unbound expr
  >>= fun () -> Ok (decorate expr)
  >>= walk Env.empty
  |>> get_var_type
)
