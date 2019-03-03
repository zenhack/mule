open Ast
module Js = Ast.Js.Expr
module DE = Ast.Desugared.Expr
module D = Ast.Desugared

let rec toJs = function
  | DE.Var v ->
      Js.Var v
  | DE.Lam (param, body) ->
      Js.Func(param, toJs body)
  | DE.App (f, x) ->
      Js.App(toJs f, [toJs x])
  | DE.Let(v, e, body) ->
      toJs (DE.App (DE.Lam(v, body), e))
  | DE.Record fields ->
      D.RowMap.bindings fields
        |> List.map
            (fun (l, e) -> (Label.to_string l, toJs e))
        |> fun fields' -> Js.Object fields'
  | DE.GetField (e, l) ->
      Js.GetProp(toJs e, Js.String (Label.to_string l))
  | DE.Update(e, changes) ->
      Js.App
        ( Js.Var (Var.of_string "$mulecp")
        , [ toJs e
          ; Js.Object
              ( List.map
                  (fun (l, v) ->
                    ( Label.to_string l
                    , toJs v
                    )
                  )
                  changes
              )
          ]
        )
  | DE.WithType(v, _) ->
      toJs v
  | DE.Ctor (l, v) ->
      Js.Object
        [ ("$", Js.String (Label.to_string l))
        ; ("v", toJs v)
        ]
  | DE.Match {cases; default} ->
      let param = Gensym.anon_var () in
      (* We implement a match by putting a bunch of lambdas in an object,
       * and then getting the property from the object that matches the
       * ctor. *)
      let matched = Js.GetProp
        ( toJs (DE.Record (D.RowMap.map (fun (v, body) -> DE.Lam (v, body)) cases))
        , Js.GetProp (Js.Var param, String "$")
        )
      in
      let ctor_args = [Js.GetProp(Js.Var param, String "v")] in
      Js.Func
        ( param
        , begin match default with
          | None ->
              (* In this case there's no default, so it's straighforward; just
               * get the value from the object and apply it. *)
              Js.App (matched, ctor_args)
          | Some def ->
              (* There's a default, so we need to check if the value is actually
               * there.
               *
               * pseudo code, for what this is generating:
               *
               * let f = record.ctor in
               * if f === undefined then
               *   def(v)
               * else
               *   f(v)
               *
               * we're using a lambda in place of the let, and the Ternary operator
               * as an if-expression, so it's not as nice looking as that.
               *)
              let param' = Gensym.anon_var () in
              Js.App
                (Js.Func
                  ( param'
                  , Js.Ternary
                      ( Js.Eq3(Js.Var param', Js.Undefined)
                      , begin match def with
                          (* If there's a variable name for the default, we use it
                           * as the function parameter. otherwise, we can just
                           * insert the body directly, as we don't use the argument.
                           *)
                          | (Some p, body) ->
                              Js.App (Js.Func(p, toJs body), [Js.Var param])
                          | (None, body) -> toJs body
                        end
                        (* We hit one of the actual patterns; just use it: *)
                      , Js.App (Js.Var param', ctor_args)
                      )
                  )
                  , [matched]
                )
        end
        )
