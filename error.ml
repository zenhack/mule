
type t =
  | UnboundVar of Ast.var
  | TypeMismatch
  | DuplicateFields of (string list)
  | UnreachableCases

exception MuleExn of t
