open Ast.Desugared.Expr
open Ast.Desugared

exception NotAFunction
exception UnboundVar of string

let rec subst param arg expr = match expr with
  | Var (Ast.Var v) when v = param -> arg
  | Var _ -> expr
  | Ctor _ -> expr
  | Lam (Ast.Var param', body) ->
      if param == param' then
        expr
      else
        Lam (Ast.Var param', subst param arg body)
  | App (f, x) ->
      App (subst param arg f, subst param arg x)
  | Record fields ->
      Record (RowMap.map (subst param arg) fields)
  | GetField (e, lbl) ->
      GetField (subst param arg e, lbl)
  | Extend(e, fields) ->
      Extend
        ( subst param arg e
        , List.map (fun (l, v) -> (l, subst param arg v)) fields
        )

let rec eval = function
  | Var (Ast.Var v) ->
      raise (UnboundVar v)
  | Lam lam -> Lam lam
  | Ctor c -> Ctor c
  | App (f, arg) ->
      let f' = eval f in
      let arg' = eval arg in
      begin match f' with
      | Lam (Ast.Var param, body) ->
          eval (subst param arg' body)
      | _ ->
          raise NotAFunction
      end
  | Record fields ->
      Record (RowMap.map eval fields)
  | GetField (e, lbl) ->
      begin match eval e with
      | Record fields ->
          RowMap.find lbl fields
      | _ -> Debug.impossible
        ("Tried to get a field on something that's not a record. " ^
        "this should have been caught by the type checker!")
      end
  | Extend(r, new_fields) ->
      begin match eval r with
      | Record old_fields ->
          Record
            ( List.fold_left
                (fun old (l, v) -> RowMap.add l (eval v) old)
                old_fields
                new_fields
            )
      | _ -> Debug.impossible
          ("Tried to do a record update on something that's not a record. " ^
          "This should have been caught by the type checker!")
      end
