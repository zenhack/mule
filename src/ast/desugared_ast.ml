open Sexplib.Std
module Sexp = Sexplib.Sexp
open Common_ast

module RowMap : sig
  include module type of Map.Make(Label)
  val sexp_of_t : ('a -> Sexp.t) -> 'a t -> Sexp.t
end = struct
  include Map.Make(Label)

  type 'a binding = (Label.t * 'a)
  [@@deriving sexp_of]

  let sexp_of_t sexp_of_val map =
    bindings map
    |> sexp_of_list (sexp_of_binding sexp_of_val)
end

module Expr = struct
  type t =
    | Var of Var.t
    | Lam of (Var.t * t)
    | App of (t * t)
    | Record of t RowMap.t
    | GetField of (t * Label.t)
    | Update of (t * (Label.t * t) list)
    | Ctor of (Label.t * t)
    | Match of {
        cases: (Var.t * t) RowMap.t;
        default: (Var.t option * t) option;
      }
    [@@deriving sexp_of]
end

(*
module Pretty = struct
  let expr e =
    Expr.sexp_of_t e
    |> Sexp.to_string_hum
end
*)

module Pretty = struct
  let rec expr indent =
    function
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
end
