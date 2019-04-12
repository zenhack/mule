open Ast
open Ast.Desugared

let prec = function
  | `Top -> -1000
  | `App -> 0
  | `FnR | `Fn -> 1
  | `FnL -> 2
  | `Alt -> 3


let is_left = function
  | `FnL -> true
  | _ -> false

let op_parens parent child txt =
  if prec child < prec parent then
    "(" ^ txt ^ ")"
  else
    txt

let binder_parens parent txt =
  if is_left parent then
    "(" ^ txt ^ ")"
  else
    txt

let rec typ p = Type.(
  function
  | Var (_, v) -> Ast.Var.to_string v
  | Fn (_, f, x) ->
      op_parens p `Fn
        (String.concat
          [ typ `FnL f
          ; " -> "
          ; typ `FnR x
          ])
  | Recur (_, v, body) ->
      binder_parens p
        (String.concat
          [ "rec "
          ; Ast.Var.to_string v
          ; ". "
          ; typ `Top body
          ])
  | Record (_, fields, rest) ->
      String.concat
        [ "{"
        ; String.concat ~sep:", "
            (List.map fields
              ~f:(fun (lbl, ty) -> Ast.Label.to_string lbl ^ " : " ^ typ `Top ty)
            )
        ; (match rest with
            | Some v -> ", ..." ^ Ast.Var.to_string v
            | None -> "")
        ; "}"
        ]
  | Union (_, ctors, rest) -> (
      op_parens p `Alt
        (String.concat ~sep:" | "
            (List.map ctors ~f: (fun (lbl, ty) -> Ast.Label.to_string lbl ^ " " ^ typ `App ty)))
          ^ match rest with
            | Some v -> " | ..." ^ Ast.Var.to_string v
            | None -> ""
        )
  | Quant(_, q, var, _, body) ->
      let qstr = match q with
        | `All -> "all "
        | `Exist -> "exist "
      in
      binder_parens p
        (qstr ^ Var.to_string var ^ ". " ^ typ `Top body)
)
let typ t = typ `Top t

let rec expr indent = function
  | Expr.Var var ->
      Var.to_string var
  | Expr.Ctor (name, e) ->
      "(" ^ Label.to_string name ^ " " ^ expr indent e ^ ")"
  | Expr.Lam (var, body) ->
      String.concat
        [ "fn "
        ; Var.to_string var
        ; ". "
        ; expr indent body
        ]
  | Expr.App (f, x) ->
      String.concat
        [ "("
        ; expr indent f
        ; ") ("
        ; expr indent x
        ; ")"
        ]
  | Expr.EmptyRecord ->
      "{}"
  | Expr.Update lbl ->
      "(_ where { " ^ Label.to_string lbl ^ " = _ })"
  | Expr.GetField lbl ->
      "_." ^ Label.to_string lbl
  | Expr.WithType ty ->
      "(_ : " ^ typ ty ^ ")"
  | Expr.Let (v, e, body) ->
      "let " ^ Var.to_string v ^ " = " ^ expr indent e ^ " in " ^ expr indent body
  | Expr.Match {cases; default} ->
      let new_indent = indent ^ "  " in
      String.concat
        [ "match-lam"
        ; Map.to_alist cases
            |> List.map ~f:(fun (lbl, (v, e)) -> String.concat
                [ "\n"
                ; indent
                ; "| "
                ; Label.to_string lbl
                ; " "
                ; Var.to_string v
                ; " -> "
                ; expr new_indent e
                ]
            )
            |> String.concat
        ; begin match default with
            | None -> ""
            | Some (None, e) -> String.concat
                [ "\n"
                ; indent
                ; "| _ -> "
                ; expr new_indent e
                ]
            | Some (Some v, e) -> String.concat
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
