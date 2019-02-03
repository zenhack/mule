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
)

(* Check for unbound variables. *)
let check_unbound expr =
  let free = expr_free_vars S.empty expr in
  match S.find_first_opt (fun _ -> true) free with
  | Some x -> OrErr.Err (UnboundVar (Ast.Var x))
  | None -> OrErr.Ok ()

(* The type of values associated with unification variables *)
type uVal =
  | Type of int
  | Fn of (int * uVal UnionFind.var * uVal UnionFind.var)

let rec unify l r = OrErr.(
  match l, r with
  | (Fn (i, ll, lr), Fn (_, rl, rr)) ->
      UnionFind.merge unify ll rl
      >>= fun l' -> UnionFind.merge unify lr rr
      >>= fun r' -> Ok (Fn (i, l', r'))
  | (Type _, r) -> Ok r
  | (l, Type _) -> Ok l
)

let decorate expr =
  Ast.Expr.map_info (fun _ -> UnionFind.make (Type (Gensym.gensym ()))) expr

let rec walk env = Ast.Expr.(OrErr.(
  function
  | Var (uVar, Ast.Var v) ->
      UnionFind.merge unify uVar (Env.find v env)
  | Lam (fVar, Ast.Var param, body) ->
      let paramVar = UnionFind.make (Type (Gensym.gensym ())) in
      walk (Env.add param paramVar env) body
      >>= fun retVar ->
        UnionFind.merge unify
          fVar
          (UnionFind.make (Fn (Gensym.gensym (), paramVar, retVar)))
  | App (retVar, f, arg) ->
      walk env f
      >>= fun fVar -> walk env arg
      >>= fun argVar ->
        UnionFind.merge unify
          fVar
          (UnionFind.make (Fn (Gensym.gensym (), argVar, retVar)))
      >> Ok retVar
))


let ivar i = "t" ^ string_of_int i

let rec add_rec_binders ty = Ast.Type.(
  match ty with
  | Var (_, (Ast.Var v)) ->
      ( S.singleton v
      , ty
      )
  | Rec(i, v, t) ->
      let (vs, ts) = add_rec_binders t in
      ( S.remove (ivar i) vs
      , Rec(i, v, ts)
      )
  | Fn (i, f, x) ->
      let (fv, ft) = add_rec_binders f in
      let (xv, xt) = add_rec_binders x in
      let vars = S.union fv xv in
      let myvar = ivar i in
      if S.mem myvar vars then
        ( S.remove myvar vars
        , Rec(i, Ast.Var myvar, Fn (i, ft, xt))
        )
      else
        ( vars
        , Fn (i, ft, xt)
        )
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
