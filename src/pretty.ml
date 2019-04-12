open Ast
open Ast.Desugared

let prec = function
  | `Top -> -1000
  | `Type -> -50
  | `App | `AppL -> 0
  | `AppR -> 1
  | `FnR | `Fn -> 10
  | `FnL -> 20
  | `Alt -> 30
  | `WhereL -> 39
  | `Where -> 40

let is_left = function
  | `FnL | `AppL | `WhereL -> true
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
            (List.map ctors ~f: (fun (lbl, ty) -> Ast.Label.to_string lbl ^ " " ^ typ `AppR ty)))
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

let rec expr p indent = function
  | Expr.Var var ->
      Var.to_string var
  | Expr.Ctor (name, e) ->
      op_parens p `App
        (Label.to_string name ^ " " ^ expr `AppR indent e)
  | Expr.Lam (var, body) ->
      binder_parens p
        (String.concat
          [ "fn "
          ; Var.to_string var
          ; ". "
          ; expr `Top indent body
          ])
  | Expr.App (f, x) ->
      op_parens p `App
        (String.concat
          [ expr `AppL indent f
          ; " "
          ; expr `AppR indent x
          ])
  | Expr.EmptyRecord ->
      "{}"
  | Expr.Update lbl ->
      op_parens p `Where
        ("_ where { " ^ Label.to_string lbl ^ " = _ }")
  | Expr.GetField lbl ->
      "_." ^ Label.to_string lbl
  | Expr.WithType ty ->
      op_parens p `Type
        ("_ : " ^ typ `Type ty)
  | Expr.Let (v, e, body) ->
      binder_parens p
        ("let " ^ Var.to_string v ^ " = " ^ expr `Top indent e ^ " in " ^ expr `Top indent body)
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
                ; expr `Top new_indent e
                ]
            )
            |> String.concat
        ; begin match default with
            | None -> ""
            | Some (None, e) -> String.concat
                [ "\n"
                ; indent
                ; "| _ -> "
                ; expr `Top new_indent e
                ]
            | Some (Some v, e) -> String.concat
                [ "\n"
                ; indent
                ; "| "
                ; Var.to_string v
                ; " -> "
                ; expr `Top new_indent e
                ]
          end
        ; "\n"
        ; indent
        ; "end"
        ]
let typ t = typ `Top t
let expr e = expr `Top "" e

let rec runtime_expr p =
  let open Ast.Runtime.Expr in
  function
  | Var v -> Var.to_string v
  | Lam(param, body) ->
      binder_parens p
        ("fn " ^ Var.to_string param ^ ". " ^ runtime_expr `Top body)
  | App(f, x) ->
      op_parens p `App
        (runtime_expr `AppL f ^ " " ^ runtime_expr `AppR x)
  | Record r -> String.concat
      [ "{"
      ; Map.to_alist r
          |> List.map ~f:(fun (k, v) -> Label.to_string k ^ " = " ^ runtime_expr `Top v)
          |> String.concat ~sep:", "
      ; "}"
      ]
  | GetField label ->
      "_." ^ Label.to_string label
  | Update {old; label; field} ->
      op_parens p `Where
        (String.concat
          [ runtime_expr `WhereL old
          ; " where { "
          ; Label.to_string label
          ; " = "
          ; runtime_expr `Top field
          ; " }"
          ])
  | Ctor (label, arg) ->
      runtime_expr p
        (App
          ( Var(Var.of_string(Label.to_string label))
          , arg
          )
        )
  | Match {cases; default} ->
      String.concat
        [ "match _ with "
        ; String.concat ~sep:" | "
            (cases
              |> Map.to_alist
              |> List.map
                  ~f:(fun (lbl, f) -> Label.to_string lbl ^ " -> " ^ runtime_expr `Top f))
        ; begin match default with
            | None -> ""
            | Some f -> " | _ -> " ^ runtime_expr `Top f
          end
        ; " end"
        ]
let runtime_expr e = runtime_expr `Top e
