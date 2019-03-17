open Ast
open Ast.Desugared

let rec typ = Type.(
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
  | All(_, var, body) ->
      "all " ^ Var.to_string var ^ ". " ^ typ body
)

let rec expr indent = function
  | Expr.Var var ->
      Var.to_string var
  | Expr.Ctor (name, e) ->
      "(" ^ Label.to_string name ^ " " ^ expr indent e ^ ")"
  | Expr.Lam (var, body) ->
      String.concat ""
        [ "fn "
        ; Var.to_string var
        ; ". "
        ; expr indent body
        ]
  | Expr.App (f, x) ->
      String.concat ""
        [ "("
        ; expr indent f
        ; ") ("
        ; expr indent x
        ; ")"
        ]
  | Expr.EmptyRecord ->
      "{}"
  | Expr.Update(r, (lbl, field)) ->
      String.concat ""
        [ expr indent r
        ; " where { "
        ; Label.to_string lbl ^ " = " ^ expr indent field
        ; " }"
        ]
  | Expr.GetField (e, lbl) ->
      "(" ^ expr indent e ^ ")." ^ Label.to_string lbl
  | Expr.WithType(v, ty) ->
      "(" ^ expr indent v ^ " : " ^ typ ty ^ ")"
  | Expr.Let (v, e, body) ->
      "let " ^ Var.to_string v ^ " = " ^ expr indent e ^ " in " ^ expr indent body
  | Expr.Match {cases; default} ->
      let new_indent = indent ^ "  " in
      String.concat ""
        [ "match-lam"
        ; RowMap.to_seq cases
            |> Seq.map (fun (lbl, (v, e)) -> String.concat ""
                [ "\n"
                ; indent
                ; "| "
                ; Label.to_string lbl
                ; " "
                ; Var.to_string v
                ; " -> "
                ; expr new_indent e
                ])
            |> List.of_seq
            |> String.concat ""
        ; begin match default with
            | None -> ""
            | Some (None, e) -> String.concat ""
                [ "\n"
                ; indent
                ; "| _ -> "
                ; expr new_indent e
                ]
            | Some (Some v, e) -> String.concat ""
                [ "\n"
                ; indent
                ; "| "
                ; Var.to_string v
                ; " -> "
                ; expr new_indent e
                ]
          end
        ; "\n"
        ; indent
        ; "end"
        ]
let expr e = expr "" e
