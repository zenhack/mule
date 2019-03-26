open Common_ast

type 'a rowmap = (Label.t, 'a, Label.comparator_witness) Map.t

module Expr = struct
  type t =
    | Var of Var.t
    | Lam of (Var.t * t)
    | App of (t * t)
    | Record of t rowmap
    | GetField of Label.t
    | Update of
        { old: t
        ; label: Label.t
        ; field: t
        }
    | Ctor of (Label.t * t)
    | Match of {
        cases: t rowmap;
        default: t option;
      }

  let rec pretty = function
    | Var v -> Var.to_string v
    | Lam(param, body) ->
      "fn " ^ Var.to_string param ^ ". " ^ pretty body
    | App(f, x) ->
      "(" ^ pretty f ^ ") (" ^ pretty x ^ ")"
    | Record r -> String.concat
      [ "{"
      ; Map.to_alist r
          |> List.map ~f:(fun (k, v) -> Label.to_string k ^ " = " ^ pretty v)
          |> String.concat ~sep:", "
      ; "}"
      ]
    | GetField label ->
      "(_." ^ Label.to_string label ^ ")"
    | Update {old; label; field} ->
        String.concat
          [ "("
          ; pretty old
          ; ")"
          ; " where { "
          ; Label.to_string label
          ; " = "
          ; pretty field
          ; " }"
          ]
    | Ctor (label, arg) ->
        pretty
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
                  ~f:(fun (lbl, f) -> Label.to_string lbl ^ " -> " ^ pretty f))
        ; begin match default with
            | None -> ""
            | Some f -> " | _ -> " ^ pretty f
          end
        ; " end"
        ]
end
