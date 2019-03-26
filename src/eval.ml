open Ast.Runtime.Expr

module Var = Ast.Var
module Label = Ast.Label

let rec subst param arg expr = match expr with
  | Var v when Var.equal v param -> arg
  | Var _ -> expr
  | Ctor (lbl, value) ->
      Ctor (lbl, subst param arg value)
  | Lam (param', body) ->
      Lam (subst_binding param' param arg body)
  | App (f, x) ->
      App (subst param arg f, subst param arg x)
  | Record r ->
      Record (Map.map r ~f:(subst param arg))
  | GetField lbl ->
      GetField lbl
  | Update {old; label; field} ->
      Update
        { old = subst param arg old
        ; label
        ; field = subst param arg field
        }
  | Match {cases; default} ->
      Match
        { cases = Map.map cases ~f:(subst param arg)
        ; default = Option.map default ~f:(subst param arg)
        }
and subst_binding param' param arg body =
  if Var.equal param param' then
    (param', body)
  else
    (param', subst param arg body)


let rec eval = function
  | Var v ->
      failwith
        ("Unbound variable \"" ^ Ast.Var.to_string v ^ "\"; this should have been caught sooner.")
  | Lam lam -> Lam lam
  | Match m -> Match m
  | GetField l -> GetField l
  | Ctor c -> Ctor c
  | App (f, arg) ->
      let f' = eval f in
      let arg' = eval arg in
      begin match f' with
      | Lam (param, body) ->
          eval (subst param arg' body)
      | Match {cases; default} ->
          eval_match cases default arg'
      | GetField label ->
          begin match arg' with
            | Record r ->
                Map.find_exn r label
            | _ ->
                failwith "Tried to get field of non-record"
          end
      | _ ->
        failwith "Tried to call non-function"
      end
  | Record r ->
      Record (Map.map r ~f:eval)
  | Update {old; label; field} ->
      begin match eval old with
        | Record r -> Record (Map.set ~key:label ~data:(eval field) r)
        | _ -> failwith "Tried to set field on non-record"
      end
and eval_match cases default =
  function
 | Ctor (lbl, value) ->
     begin match Map.find cases lbl with
      | Some f ->
          eval (App(f, value))
      | None ->
        begin match default with
          | Some f ->
              eval (App(f, Ctor(lbl, value)))
          | None ->
              failwith "Match failed"
        end
     end
  | value ->
     begin match default with
       | Some f ->
           eval (App(f, value))
       | None ->
           failwith "Match failed"
     end
