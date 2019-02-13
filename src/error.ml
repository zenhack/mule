
type t =
  | UnboundVar of Ast.Var.t
  | TypeMismatch
  | DuplicateFields of (Ast.Label.t list)
  | UnreachableCases
  | EmptyMatch

exception MuleExn of t
