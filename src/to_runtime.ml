open Ast

module D = Desugared.Expr
module R = Runtime.Expr

let rec translate: int -> int VarMap.t -> D.t -> (int * R.t) =
  fun depth env -> function
  | D.Var v ->
      let n = depth - Map.find_exn env v in
      (n, R.Var n)
  | D.Fix ->
      failwith "TODO"
  | D.Lam (param, body) ->
      let (ncap, body') =
        translate (depth + 1) (Map.set env ~key:param ~data:(depth + 1)) body
      in
      (ncap, R.Lam(ncap, [], body'))
  | D.App(D.WithType _, e) -> translate depth env e
  | D.App(f, x) ->
      let (fcap, f') = translate depth env f in
      let (xcap, x') = translate depth env x in
      (max fcap xcap, R.App(f', x'))
  | D.WithType _ ->
      (0, R.Lam(0, [], R.Var 0))
  | D.EmptyRecord -> (0, R.Record LabelMap.empty)
  | D.GetField lbl -> (0, R.GetField lbl)
  | D.Update label ->
      ( 0
      , R.Lam(0, [], R.Lam(1, [], R.Update { old = R.Var 1; label; field = R.Var 0 }))
      )
  | D.Ctor (label, e) ->
      let (ncap, e') = translate depth env e in
      (ncap, R.Ctor(label, e'))
  | D.Match{cases; default} ->
      let cases' = Map.map
          cases
          ~f:(fun (param, body) -> translate depth env (D.Lam(param, body)))
      in
      let (defcaps, default') = match default with
          | None -> (0, None)
          | Some (None, body) ->
              let (ncaps, body') = translate depth env (D.Lam(Gensym.anon_var(), body)) in
              (ncaps, Some body')
          | Some(Some param, body) ->
              let (ncaps, body') = translate depth env (D.Lam(param, body)) in
              (ncaps, Some body')
      in
      let ncaps = Map.fold
        ~init:defcaps
        ~f:(fun ~key:_ ~data -> max data)
        (Map.map cases' ~f:fst)
      in
      ( ncaps
      , R.Match
        { cases = Map.map ~f:snd cases'
        ; default = default'
        }
      )
  | D.Let (v, e, body) ->
      translate depth env (D.App (D.Lam (v, body), e))

let translate: D.t -> R.t =
  fun exp -> snd (translate 0 VarMap.empty exp)
