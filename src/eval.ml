open Ast.Desugared.Expr
open Ast.Desugared

let rec subst param arg expr = match expr with
  | Var v when v = param -> arg
  | Var _ -> expr
  | Ctor (lbl, value) ->
      Ctor (lbl, subst param arg value)
  | Lam (param', body) ->
      Lam (subst_binding param' param arg body)
  | Let(param', e, body) when param == param' ->
      Let(param', e, body)
  | Let(param', e, body) ->
      Let(param', subst param arg e, subst param arg body)
  | App (f, x) ->
      App (subst param arg f, subst param arg x)
  | Record fields ->
      Record (RowMap.map (subst param arg) fields)
  | GetField (e, lbl) ->
      GetField (subst param arg e, lbl)
  | Update(e, (lbl, field)) ->
      Update
        ( subst param arg e
        , (lbl, subst param arg field)
        )
  | Match {cases; default} ->
      Match
        { cases = RowMap.map
          (fun (param', body) ->
            subst_binding param' param arg body)
          cases
        ; default = match default with
            | None ->
                None
            | Some (Some param', body) ->
                let (p', b') = subst_binding param' param arg body in
                Some (Some p', b')
            | Some (None, body) ->
                Some (None, subst param arg body)
        }
  | WithType (v, _) ->
      subst param arg v
and subst_binding param' param arg body =
  if param == param' then
    (param', body)
  else
    (param', subst param arg body)


let rec eval = function
  | Var v ->
      failwith
        ("Unbound variable \"" ^ Ast.Var.to_string v ^ "\"; this should have been caught sooner.")
  | Lam lam -> Lam lam
  | Match m -> Match m
  | Ctor c -> Ctor c
  | App (f, arg) ->
      let f' = eval f in
      let arg' = eval arg in
      begin match f' with
      | Lam (param, body) ->
          eval (subst param arg' body)
      | Match {cases; default} ->
          eval_match cases default arg'
      | _ ->
        failwith ("Tried to call non-function: " ^ Pretty.expr f')
      end
  | Record fields ->
      Record (RowMap.map eval fields)
  | GetField (e, lbl) ->
      begin match eval e with
      | Record fields ->
          RowMap.find lbl fields
      | _ -> failwith
        ("Tried to get a field on something that's not a record. " ^
        "this should have been caught by the type checker!")
      end
  | Update(r, (lbl, field)) ->
      begin match eval r with
      | Record old_fields ->
          Record (RowMap.add lbl (eval field) old_fields)
      | _ -> failwith
          ("Tried to do a record update on something that's not a record. " ^
          "This should have been caught by the type checker!")
      end
  | Let(v, e, body) ->
      eval (subst v (eval e) body)
  | WithType(v, _) ->
      eval v
and eval_match cases default = function
 | Ctor (lbl, value) ->
     begin match RowMap.find_opt lbl cases with
      | Some (param, body) ->
        eval (subst param value body)
      | None ->
        begin match default with
          | None ->
              failwith "Match failed"
          | Some (None, body) ->
              eval body
          | Some (Some param, body) ->
              eval (subst param (Ctor (lbl, value)) body)
        end
     end
  | value ->
      begin match default with
        | None ->
            failwith "Match failed"
        | Some (None, body) ->
            eval body
        | Some (Some param, body) ->
            eval (subst param value body)
      end
