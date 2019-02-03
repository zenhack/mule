open Ast.Expr

exception NotAFunction
exception UnboundVar of string

let rec subst param arg expr = match expr with
  | Var (_, Ast.Var v) when v = param -> arg
  | Var _ -> expr
  | Lam (i, Ast.Var param', body) ->
      if param == param' then
        expr
      else
        Lam (i, Ast.Var param', subst param arg body)
  | App (i, f, x) ->
      App (i, subst param arg f, subst param arg x)
  | Record _ -> Debug.todo "Substitute records"

let rec eval = function
  | Var (_, Ast.Var v) ->
      raise (UnboundVar v)
  | Lam lam -> Lam lam
  | App (_, f, arg) ->
      let f' = eval f in
      let arg' = eval arg in
      begin match f' with
      | Lam (_, (Ast.Var param), body) ->
          eval (subst param arg' body)
      | _ ->
          raise NotAFunction
      end
  | Record _ -> Debug.todo "Evaluate records"
