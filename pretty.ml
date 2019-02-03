open Ast

let rec expr = function
  | EVar (_, Var name) ->
      name
  | ELam (_, Var name, body) ->
      String.concat ""
        [ "fn "
        ; name
        ; ". "
        ; expr body
        ]
  | EApp (_, f, x) ->
      String.concat ""
        [ "("
        ; expr f
        ; ") ("
        ; expr x
        ; ")"
        ]

let rec typ = function
  | TVar (_, Var v) -> v
  | TFn (_, f, x) ->
      String.concat ""
        [ "("
        ; typ f
        ; " -> "
        ; typ x
        ; ")"
        ]
  | TRec (_, Var v, body) ->
      String.concat ""
        [ "rec "
        ; v
        ; ". "
        ; typ body
        ]
