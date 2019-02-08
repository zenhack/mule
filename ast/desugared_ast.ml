open Common_ast

module RowMap = Map.Make(struct
  type t = label

  let compare (Label l) (Label r) = String.compare l r
end)

module Expr = struct
  type t =
    | Var of var
    | Lam of (var * t)
    | App of (t * t)
    | Record of t RowMap.t
    | GetField of (t * label)
    | Update of (t * (label * t) list)
    | Ctor of (label * t)
    | Match of {
        cases: (var * t) RowMap.t;
        default: (var option * t) option;
      }
end

module Pretty = struct
  let rec expr indent =
    function
    | Expr.Var (Var name) ->
        name
    | Expr.Ctor (Label name, e) ->
        "(" ^ name ^ " " ^ expr indent e ^ ")"
    | Expr.Lam (Var name, body) ->
        String.concat ""
          [ "fn "
          ; name
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
              |> Seq.map (fun (Label lbl, e) -> lbl ^ " = " ^ expr indent e)
              |> List.of_seq
              |> String.concat ", "
          ; "}"
          ]
    | Expr.Update(r, fields) ->
        String.concat ""
          [ expr indent r
          ; " where { "
          ; String.concat ", "
              (List.map (fun (Label lbl, e) -> lbl ^ " = " ^ expr indent e) fields)
          ; " }"
          ]
    | Expr.GetField (e, Label lbl) ->
        "(" ^ expr indent e ^ ")." ^ lbl
    | Expr.Match {cases; default} ->
        let new_indent = indent ^ "  " in
        String.concat ""
          [ "match-lam"
          ; RowMap.to_seq cases
              |> Seq.map (fun (Label lbl, (Var v, e)) -> String.concat ""
                  [ "\n"
                  ; indent
                  ; "| "
                  ; lbl
                  ; " "
                  ; v
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
              | Some (Some (Var v), e) -> String.concat ""
                  [ "\n"
                  ; indent
                  ; "| "
                  ; v
                  ; " -> "
                  ; expr new_indent e
                  ]
            end
          ; "\n"
          ; indent
          ; "end"
          ]
  let expr e = expr "" e
end
