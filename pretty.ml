let rec expr = Ast.Expr.(
  function
  | Var (_, Ast.Var name) ->
      name
  | Lam (_, Ast.Var name, body) ->
      String.concat ""
        [ "fn "
        ; name
        ; ". "
        ; expr body
        ]
  | App (_, f, x) ->
      String.concat ""
        [ "("
        ; expr f
        ; ") ("
        ; expr x
        ; ")"
        ]
  | Record _ ->
      Debug.todo "print records"
)

let rec typ = Ast.Type.(
  function
  | Var (_, Ast.Var v) -> v
  | Fn (_, f, x) ->
      String.concat ""
        [ "("
        ; typ f
        ; ") -> ("
        ; typ x
        ; ")"
        ]
  | Recur (_, Ast.Var v, body) ->
      String.concat ""
        [ "rec "
        ; v
        ; ". "
        ; typ body
        ]
  | Record _ ->
      Debug.todo "Print record types"
)
