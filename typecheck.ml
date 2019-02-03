include Typecheck_t

module S = Set.Make(String)
module Env = Map.Make(String)

let rec free_vars env = Ast.Expr.(
  function
  | Var (_, Ast.Var v) ->
      if S.mem v env then
        S.empty
      else
        S.singleton v
  | Lam (_, Ast.Var v, body) ->
      free_vars (S.add v env) body
  | App (_, f, x) ->
      S.union (free_vars env f) (free_vars env x)
)

let check_unbound expr =
  let free = free_vars S.empty expr in
  match S.find_first_opt (fun _ -> true) free with
  | Some x -> OrErr.Err (UnboundVar (Ast.Var x))
  | None -> OrErr.Ok ()

(* The type of values associated with unification variables *)
type uVal =
  | Free of int
  | Fn of (int * uVal UnionFind.var * uVal UnionFind.var)

let get_index = function
  | Free i -> i
  | Fn (i, _, _) -> i

let rec unify l r = OrErr.(
  match l r with
  | (Fn (i, ll, lr), Fn (_, rl, rr)) ->
      UnionFind.merge unify ll rl
      >>= fun l' -> UnionFind.merge unify lr rr
      >>= fun r' -> Ok (i, l', r')
  | (Free _, r) -> Ok r
  | (l, Free _) -> Ok l
)

let decorate expr =
  Ast.Expr.map_info (fun _ -> UnionFind.make (Free (gensym ()))) expr

let walk env = Ast.Expr.(
  function
  | Var (uVar, Ast.Var v) ->
      UnionFind.merge unify uVar (Env.find v env)
  | Lam (fVar, Ast.Var param, body) ->
      let paramVar = UnionFind.make (Free (gensym ())) in
      walk (Env.add param paramVar) body
      >>= fun retVar ->
        UnionFind.merge unify
          fVar
          (UnionFind.make (Fn (gensym (), paramVar, retVar)))
  | EApp (retVar, f, arg) ->
      walk env f
      >>= fun fVar -> walk env arg
      >>= fun argVar ->
        UnionFind.merge unify
          fVar
          (UnionFind.make (Fn (gensym(), argVar, retVar)))
      |>> retVar
)

let typecheck expr =
  check_unbound expr
  >>= walk Env.empty
