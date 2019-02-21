open Ast
open Ast.Desugared

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
  | Expr.Record fields ->
      String.concat ""
        [ "{"
        ; RowMap.to_seq fields
            |> Seq.map (fun (lbl, e) -> Label.to_string lbl ^ " = " ^ expr indent e)
            |> List.of_seq
            |> String.concat ", "
        ; "}"
        ]
  | Expr.Update(r, fields) ->
      String.concat ""
        [ expr indent r
        ; " where { "
        ; String.concat ", "
            (List.map (fun (lbl, e) -> Label.to_string lbl ^ " = " ^ expr indent e) fields)
        ; " }"
        ]
  | Expr.GetField (e, lbl) ->
      "(" ^ expr indent e ^ ")." ^ Label.to_string lbl
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

let rec monotype = Type.(
  function
  | Var (_, v) -> Ast.Var.to_string v
  | Fn (_, f, x) ->
      String.concat ""
        [ "("
        ; monotype f
        ; ") -> ("
        ; monotype x
        ; ")"
        ]
  | Recur (_, v, body) ->
      String.concat ""
        [ "rec "
        ; Ast.Var.to_string v
        ; ". "
        ; monotype body
        ]
  | Record (_, fields, rest) ->
      String.concat ""
        [ "{"
        ; String.concat ", "
            (List.map
              (fun (lbl, ty) -> Ast.Label.to_string lbl ^ " : " ^ monotype ty)
              fields
            )
        ; (match rest with
            | Some v -> ", ..." ^ Ast.Var.to_string v
            | None -> "")
        ; "}"
        ]
  | Union (_, ctors, rest) -> (
      (String.concat " | "
        (List.map (fun (lbl, ty) -> "(" ^ Ast.Label.to_string lbl ^ " " ^ monotype ty ^ ")") ctors))
      ^ match rest with
        | Some v -> " | ..." ^ Ast.Var.to_string v
        | None -> ""
  )
)