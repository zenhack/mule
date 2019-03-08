
type op = [ `Graft | `Merge | `Raise | `Weaken ]
type ctor =
  [ `Fn | `Record | `Union (* types *)
  | `Empty | `Extend (* rows *)
  ]
type type_error
  = MismatchedCtors of (ctor * ctor)
  | PermissionErr of op

type t =
  | UnboundVar of Ast.Var.t
  | TypeError of type_error
  | DuplicateFields of (Ast.Label.t list)
  | UnreachableCases
  | EmptyMatch
  | MalformedType of string

exception MuleExn of t

let show_ctor = function
  | `Fn -> "function"
  | `Record -> "record"
  | `Union -> "union"
  | `Empty -> "empty row"
  | `Extend -> "non-empty row"

let show_op = function
  | `Graft -> "graft"
  | `Merge -> "merge"
  | `Raise -> "raise"
  | `Weaken -> "weaken"

let show_type_error = function
  | MismatchedCtors (l, r) ->
      "mismatched type constructors: " ^ show_ctor l ^ " and " ^ show_ctor r
  | PermissionErr op ->
      "permission error during " ^ show_op op

let show = function
  | UnboundVar var ->
      "unbound variable: " ^ Ast.Var.to_string var
  | MalformedType msg ->
      "malformed_type: " ^ msg
  | TypeError e ->
      "Type error: " ^ show_type_error e
  | UnreachableCases ->
      "Unreachable cases in match"
  | DuplicateFields fields ->
      "Duplicate fields:\n" ^
        (fields
          |> List.map Ast.Label.to_string
          |> String.concat ",")
  | EmptyMatch ->
      "Empty match expression."
