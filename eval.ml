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
  | Record (i, fields) ->
      Record (i, subst_fields param arg fields)
  | GetField (i, e, lbl) ->
      GetField (i, subst param arg e, lbl)
and subst_fields param arg = function
  | [] -> []
  | (lbl, e) :: rest -> (lbl, subst param arg e) :: subst_fields param arg rest


let rec get_field lbl = function
  | [] -> Debug.impossible "Missing field! the type checker should have caught this!"
  | ((l, v) :: rest) ->
      if lbl = l then
        v
      else
        get_field lbl rest

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
  | Record (i, fields) ->
      Record
        ( i
        , List.map
            (fun (lbl, ex) -> (lbl, eval ex))
            fields
        )
  | GetField (_, e, lbl) ->
      match eval e with
      | Record (_, fields) ->
          get_field lbl fields
      | _ -> Debug.impossible
        ("Tried to get a field on something that's not a record. " ^
        "this should have been caught by the type checker!")
