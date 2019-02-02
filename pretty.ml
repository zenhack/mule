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
