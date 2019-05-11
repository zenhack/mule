
type op = [ `Graft | `Merge | `Raise | `Weaken ]
type ctor =
  [ `Named of string
  | `Extend of Ast.Label.t
  ]
type kind = [ `Row | `Type ]
type type_error
  = MismatchedCtors of (ctor * ctor)
  | MismatchedKinds of (kind * kind)
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
  | `Named name -> name
  | `Extend lbl -> "row containing " ^ Ast.Label.to_string lbl

let show_op = function
  | `Graft -> "graft"
  | `Merge -> "merge"
  | `Raise -> "raise"
  | `Weaken -> "weaken"

let show_kind = function
  | `Type -> "type"
  | `Row -> "row"

let show_type_error = function
  | MismatchedCtors (l, r) ->
      "mismatched type constructors: " ^ show_ctor l ^ " and " ^ show_ctor r
  | MismatchedKinds (l, r) ->
      "mismatched kinds: " ^ show_kind l ^ " and " ^ show_kind r
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
          |> List.map ~f:Ast.Label.to_string
          |> String.concat ~sep:",")
  | EmptyMatch ->
      "Empty match expression."
