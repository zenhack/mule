open Ast

module D = Desugared.Expr
module R = Runtime.Expr

let rec translate: D.t -> R.t =
  fun env -> function
    | D.Var v -> R.v
    | D.Lam (param, body) -> R.Lam(param, translate body)
    | D.App(f, x) -> R.App(translate f, translate x)
    | D.EmptyRecord -> R.Record (Map.empty (module Label))
    | D.GetField (record, lbl) -> R.App(R.GetField lbl, translate record)
    | D.Update(old, label, field) -> R.(Update {old; label; field})
    | D.Ctor (label, e) -> R.Ctor(label, translate e)
    | D.Match{cases; default} ->
        R.Match
          { cases = Map.map ~f:translate cases
          ; default = begin match default with
              | None -> R.PrimFn (fun _ -> failwith "impossible")
              | Some (None, body) ->
                  let body' = translate body in
                  R.PrimFn(fun _ -> body')
              | Some(Some param, body) ->
                  R.Lam(param, translate body)
            end
          }
    | D.WithType(e, _) -> translate e
    | D.Let (v, e, body) -> R.App (R.Lam (v, body), e)
