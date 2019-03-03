
type t =
  | UnboundVar of Ast.Var.t
  | TypeMismatch
  | DuplicateFields of (Ast.Label.t list)
  | UnreachableCases
  | EmptyMatch
  | MalformedType of string

exception MuleExn of t
