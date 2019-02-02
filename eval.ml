open Ast

exception NotAFunction
exception UnboundVar of string

let rec subst param arg expr = match expr with
  | EVar (_, Var v) when v = param -> arg
  | EVar _ -> expr
  | ELam (i, Var param', body) ->
      if param == param' then
        expr
      else
        ELam (i, Var param', subst param arg body)
  | EApp (i, f, x) ->
      EApp (i, subst param arg f, subst param arg x)

let rec eval = function
  | EVar (_, Var v) ->
      raise (UnboundVar v)
  | ELam lam -> ELam lam
  | EApp (_, f, arg) ->
      let f' = eval f in
      let arg' = eval arg in
      begin match f' with
      | ELam (_, (Var param), body) ->
          eval (subst param arg' body)
      | _ ->
          raise NotAFunction
      end
