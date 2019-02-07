open Ast.Desugared.Expr
open Ast.Desugared

let rec subst param arg expr = match expr with
  | Var (Ast.Var v) when v = param -> arg
  | Var _ -> expr
  | Ctor (lbl, value) ->
      Ctor (lbl, subst param arg value)
  | Lam (Ast.Var param', body) ->
      Lam (subst_binding param' param arg body)
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
  | Match {cases; default} ->
      Match
        { cases = RowMap.map
          (fun (Ast.Var param', body) ->
            subst_binding param' param arg body)
          cases
        ; default = match default with
            | None ->
                None
            | Some (Some (Ast.Var param'), body) ->
                let (p', b') = subst_binding param' param arg body in
                Some (Some p', b')
            | Some (None, body) ->
                Some (None, subst param arg body)
        }
and subst_binding param' param arg body =
  if param == param' then
    (Ast.Var param', body)
  else
    (Ast.Var param', subst param arg body)


let rec eval = function
  | Var (Ast.Var v) ->
      Debug.impossible
        ("Unbound variable \"" ^ v ^ "\"; this should have been caught sooner.")
  | Lam lam -> Lam lam
  | Match m -> Match m
  | Ctor c -> Ctor c
  | App (f, arg) ->
      let f' = eval f in
      let arg' = eval arg in
      begin match f' with
      | Lam (Ast.Var param, body) ->
          eval (subst param arg' body)
      | Match {cases; default} ->
          eval_match cases default arg'
      | _ ->
        Debug.impossible ("Tried to call non-function: " ^ Pretty.expr f')
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
and eval_match cases default = function
 | Ctor (lbl, value) ->
     begin match RowMap.find_opt lbl cases with
      | Some (Ast.Var param, body) ->
        eval (subst param value body)
      | None ->
        begin match default with
          | None ->
              Debug.impossible "Match failed"
          | Some (None, body) ->
              eval body
          | Some (Some (Ast.Var param), body) ->
              eval (subst param value body)
        end
     end
  | value ->
      begin match default with
        | None ->
            Debug.impossible "Match failed"
        | Some (None, body) ->
            eval body
        | Some (Some (Ast.Var param), body) ->
            eval (subst param value body)
      end
