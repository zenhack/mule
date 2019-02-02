open Ast

let rec format = function
  | EVar (_, Var name) ->
      name
  | ELam (_, Var name, body) ->
      String.concat ""
        [ "fn "
        ; name
        ; ". "
        ; format body
        ]
  | EApp (_, f, x) ->
      String.concat ""
        [ "("
        ; format f
        ; ") ("
        ; format x
        ; ")"
        ]
