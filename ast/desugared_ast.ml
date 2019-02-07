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
    | Extend of (t * (label * t) list)
    | Ctor of (label * t)
end

module Pretty = struct
  let rec expr =
    function
    | Expr.Var (Var name) ->
        name
    | Expr.Ctor (Label name, e) ->
        "(" ^ name ^ " " ^ expr e ^ ")"
    | Expr.Lam (Var name, body) ->
        String.concat ""
          [ "fn "
          ; name
          ; ". "
          ; expr body
          ]
    | Expr.App (f, x) ->
        String.concat ""
          [ "("
          ; expr f
          ; ") ("
          ; expr x
          ; ")"
          ]
    | Expr.Record fields ->
        String.concat ""
          [ "{"
          ; RowMap.to_seq fields
              |> Seq.map (fun (Label lbl, e) -> lbl ^ " = " ^ expr e)
              |> List.of_seq
              |> String.concat ", "
          ; "}"
          ]
    | Expr.Extend(r, fields) ->
        String.concat ""
          [ expr r
          ; " with { "
          ; String.concat ", "
              (List.map (fun (Label lbl, e) -> lbl ^ " = " ^ expr e) fields)
          ; " }"
          ]
    | Expr.GetField (e, Label lbl) ->
        "(" ^ expr e ^ ")." ^ lbl
end
