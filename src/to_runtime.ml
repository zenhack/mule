open Ast

module D = Desugared.Expr
module R = Runtime.Expr

type binding = [ `Index of int | `Term of R.t ]

let rec translate: int -> binding VarMap.t -> D.t -> (int * R.t) =
  fun depth env -> function
    | D.Integer n -> (0, R.Integer n)
    | D.Var v ->
      begin match Map.find_exn env v with
        | `Index m ->
          let n = depth - m in
          (n, R.Var n)
        | `Term t -> (0, t)
      end
    | D.Fix flag ->
      (0, R.Fix flag)
    | D.Lam (param, body) ->
      let (ncap, body') =
        translate (depth + 1) (Map.set env ~key:param ~data:(`Index (depth + 1))) body
      in
      (ncap, R.Lam(ncap, [], body'))
    | D.App(D.Fix `Record, f) ->
      translate_fix_rec depth env f
    | D.App(D.WithType _, e) -> translate depth env e
    | D.App(f, x) ->
      let (fcap, f') = translate depth env f in
      let (xcap, x') = translate depth env x in
      (max fcap xcap, R.App(f', x'))
    | D.WithType _ ->
      (0, R.Lam(0, [], R.Var 0))
    | D.EmptyRecord -> (0, R.Record LabelMap.empty)
    | D.GetField (mode, lbl) -> (0, R.GetField (mode, lbl))
    | D.Update label ->
      ( 0
      , R.Lam(0, [], R.Lam(1, [], R.Update { old = R.Var 1; label; field = R.Var 0 }))
      )
    | D.Ctor (label, e) ->
      let (ncap, e') = translate depth env e in
      (ncap, R.Ctor(label, e'))
    | D.IntMatch{im_cases; im_default} ->
      let cases = Map.map im_cases ~f:(translate depth env) in
      let (n, def) = translate depth env im_default in
      let ncaps = Map.fold
          cases
          ~init:n
          ~f:(fun ~key:_ ~data:(next, _) prev -> max next prev)
      in
      ( ncaps
      , R.IntMatch
          { im_cases = Map.map cases ~f:snd
          ; im_default = def
          }
      )
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
    | D.LetType(_, _, body) ->
      translate depth env body
and translate_fix_rec depth env = function
  | D.Lam(v, body) ->
    let (n, lblmap) =
      translate_record_body
        (depth + 1)
        (Map.set env ~key:v ~data:(`Index (depth + 1)))
        body
    in
    ( n - 1
    , R.App
        ( R.Fix `Record
        , R.Lam(n, [], R.Record lblmap)
        )
    )
  | _ ->
    failwith "BUG"
and translate_record_body depth env = function
  | D.EmptyRecord ->
    (0, LabelMap.empty)
  | D.App(D.App(D.Update lbl, old), field) ->
    let (n, head) = translate depth env field in
    let (m, tail) = translate_record_body depth env old in
    (max n m, Map.set tail ~key:lbl ~data:head)
  | _ ->
    failwith "BUG"

let translate: D.t -> R.t =
  fun exp ->
    let env = Map.map Intrinsics.intrinsics ~f:(fun x -> `Term (snd x)) in
    snd (translate 0 env exp)
