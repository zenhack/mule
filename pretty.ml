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
  | Record (_, fields) ->
      String.concat ""
        [ "{"
        ; String.concat ", "
            (List.map
              (fun (Ast.Label lbl, e) -> lbl ^ " = " ^ expr e)
              fields
            )
        ; "}"
        ]
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
  | Record (_, fields, rest) ->
      String.concat ""
        [ "{"
        ; String.concat ", "
            (List.map
              (fun (Ast.Label lbl, ty) -> lbl ^ " : " ^ typ ty)
              fields
            )
        ; (match rest with
            | Some (Ast.Var v) -> " | " ^ v
            | None -> "")
        ; "}"
        ]
)
