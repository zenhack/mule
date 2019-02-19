module Js = Ast.Js
module D = Ast.Desugared
open Ast

let rec toJs = function
  | D.Var v ->
      Js.Var v
  | D.Lam (param, body) ->
      Js.Func(param, toJs body)
  | D.App (f, x) ->
      Js.App(toJs f, [toJs x])
  | D.Record fields ->
      D.RowMap.bindings fields
        |> List.map
            (fun (l, e) -> (Label.to_string l, toJs e))
        |> fun fields' -> Js.Object fields'
  | D.GetField (e, l) ->
      Js.GetProp(toJs e, Js.String (Label.to_string l))
  | D.Update(e, changes) ->
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
              )
          ]
        )
  | D.Ctor (l, v) ->
      Js.Object
        [ ("$", Js.String (Label.to_string l))
        ; ("v", toJs v)
        ]
  | D.Match {cases; default} ->
      let param = Gensym.anon_var () in
      (* We implement a match by putting a bunch of lambdas in an object,
       * and then getting the property from the object that matches the
       * ctor. *)
      let matched = Js.GetProp
        ( toJs (D.Record (RowMap.map (fun (v, body) -> D.Lam (v, body)) cases))
        , Js.GetProp (tmp, String "$")
        )
      in
      let args = [Js.GetProp(param, String "v")] in
      Js.Func
        ( param
        , begin match default with
          | None ->
              (* In this case there's no default, so it's straighforward; just
               * get the value from the object and apply it. *)
              Js.App (matched, args)
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
              let param' = Gensym.annon_var () in
              Js.App
                (Js.Func
                  ( param'
                  , Js.Ternary
                      ( Js.Eq3(param', Js.Undefined)
                      , begin match def with
                          (* If there's a variable name for the default, we use it
                           * as the function parameter. otherwise, we can just
                           * insert the body directly, as we don't use the argument.
                           *)
                          | (Some p, body) -> Js.App (Js.Func(p, toJs body), args)
                          | (None, body) -> toJs body
                        end
                        (* We hit one of the actually patterns; just use it: *)
                      , Js.App (param', matched)
                      )
                  )
                , matched
                )
        end
        )
