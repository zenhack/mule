
type t =
  | UnboundVar of Ast.var
  | TypeMismatch
  | DuplicateFields of (string list)
