
type origin =
  | SurfaceExpr of Surface_ast.Expr.t
  | SurfaceType of Surface_ast.Type.t
  | SurfacePattern of Surface_ast.Pattern.t

type context = {
  resolve_embed_exn: string -> string;
}
