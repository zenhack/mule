

type 'i error =
  | UnboundVar of Ast.var
  | Mismatch
