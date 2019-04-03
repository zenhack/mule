open Ast

module D = Desugared.Expr
module R = Runtime.Expr

let rec translate: D.t -> R.t = function
  | D.Var v -> R.Var v
  | D.Lam (param, body) -> R.Lam(param, translate body)
  | D.App(D.WithType _, e) -> translate e
  | D.App(f, x) -> R.App(translate f, translate x)
  | D.WithType _ ->
      let v = Gensym.anon_var () in
      R.Lam(v, R.Var v)
  | D.EmptyRecord -> R.Record (Map.empty (module Label))
  | D.GetField lbl -> R.GetField lbl
  | D.Update label ->
      let old = Gensym.anon_var () in
      let field = Gensym.anon_var () in
      R.Lam(old, R.Lam(field, R.Update { old = R.Var old; label; field = R.Var field }))
  | D.Ctor (label, e) -> R.Ctor(label, translate e)
  | D.Match{cases; default} ->
      R.Match
        { cases = Map.map cases ~f:(fun (param, body) -> R.Lam(param, translate body))
        ; default = begin match default with
            | None -> None
            | Some (None, body) ->
                Some (R.Lam(Gensym.anon_var (), translate body))
            | Some(Some param, body) ->
                Some(R.Lam(param, translate body))
          end
        }
  | D.Let (v, e, body) -> R.App (R.Lam (v, translate body), translate e)
