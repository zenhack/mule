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

(* Free variables in a type expression *)
let rec type_free_vars env = Ast.Type.(
  function
  | Var (_, (Ast.Var v))->
      if S.mem v env then
        S.empty
      else
        S.singleton v
  | Rec (_, (Ast.Var v), body) ->
      type_free_vars (S.add v env) body
  | Fn (_, l, r) ->
      S.union (type_free_vars env l) (type_free_vars env r)
)

(* Check for unbound variables. *)
let check_unbound expr =
  let free = expr_free_vars S.empty expr in
  match S.find_first_opt (fun _ -> true) free with
  | Some x -> OrErr.Err (UnboundVar (Ast.Var x))
  | None -> OrErr.Ok ()

(* The type of values associated with unification variables *)
type uVal =
  | Free of int
  | Fn of (int * uVal UnionFind.var * uVal UnionFind.var)

let rec unify l r = OrErr.(
  match l, r with
  | (Fn (i, ll, lr), Fn (_, rl, rr)) ->
      UnionFind.merge unify ll rl
      >>= fun l' -> UnionFind.merge unify lr rr
      >>= fun r' -> Ok (Fn (i, l', r'))
  | (Free _, r) -> Ok r
  | (l, Free _) -> Ok l
)

let decorate expr =
  Ast.Expr.map_info (fun _ -> UnionFind.make (Free (Gensym.gensym ()))) expr

let rec walk env = Ast.Expr.(OrErr.(
  function
  | Var (uVar, Ast.Var v) ->
      UnionFind.merge unify uVar (Env.find v env)
  | Lam (fVar, Ast.Var param, body) ->
      let paramVar = UnionFind.make (Free (Gensym.gensym ())) in
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

let rec extract_type env = function
  | Free i -> Ast.Type.Var (i, Ast.Var (ivar i))
  | Fn (i, f, x) ->
      if S.mem (ivar i) env then
        extract_type env (Free i)
      else
        let env' = S.add (ivar i) env in
        Fn
          ( i
          , extract_type env' (UnionFind.get f)
          , extract_type env' (UnionFind.get x)
          )

let extract_type uvar =
  let uval = UnionFind.get uvar in
  let ty = extract_type S.empty uval in
  match uval with
    | Free _ -> ty
    | Fn (i, _, _) ->
        let free_vars = type_free_vars S.empty ty in
        if S.mem (ivar i) free_vars then
          Ast.Type.Rec (i, Ast.Var (ivar i), ty)
        else
          ty

let typecheck expr = OrErr.(
  check_unbound expr
  >>= fun () -> Ok (decorate expr)
  >>= walk Env.empty
  |>> extract_type
)
