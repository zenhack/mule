
(*
let typ t =
  Ast.Surface.Type.sexp_of_t (fun _ -> sexp_of_unit ()) t
  |> Sexplib.Sexp.to_string_hum
  *)
let rec typ = Ast.Surface.Type.(
  function
  | Var (_, v) -> Ast.Var.to_string v
  | Fn (_, f, x) ->
      String.concat ""
        [ "("
        ; typ f
        ; ") -> ("
        ; typ x
        ; ")"
        ]
  | Recur (_, v, body) ->
      String.concat ""
        [ "rec "
        ; Ast.Var.to_string v
        ; ". "
        ; typ body
        ]
  | Record (_, fields, rest) ->
      String.concat ""
        [ "{"
        ; String.concat ", "
            (List.map
              (fun (lbl, ty) -> Ast.Label.to_string lbl ^ " : " ^ typ ty)
              fields
            )
        ; (match rest with
            | Some v -> ", ..." ^ Ast.Var.to_string v
            | None -> "")
        ; "}"
        ]
  | Union (_, ctors, rest) -> (
      (String.concat " | "
        (List.map (fun (lbl, ty) -> "(" ^ Ast.Label.to_string lbl ^ " " ^ typ ty ^ ")") ctors))
      ^ match rest with
        | Some v -> " | ..." ^ Ast.Var.to_string v
        | None -> ""
  )
)
