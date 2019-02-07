
let rec typ = Ast.Surface.Type.(
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
            | Some (Ast.Var v) -> ", ..." ^ v
            | None -> "")
        ; "}"
        ]
  | Union (_, ctors, rest) -> (
      (String.concat " | "
        (List.map (fun (Ast.Label lbl, ty) -> "(" ^ lbl ^ " " ^ typ ty ^ ")") ctors))
      ^ match rest with
        | Some (Ast.Var v) -> " | ..." ^ v
        | None -> ""
  )
)
