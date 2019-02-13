
type t =
  | UnboundVar of Ast.var
  | TypeMismatch
  | DuplicateFields of (Ast.Label.t list)
  | UnreachableCases
  | EmptyMatch

exception MuleExn of t
