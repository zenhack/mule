
type origin =
  | SurfaceExpr of Surface_ast.Expr.t
  | SurfaceType of Surface_ast.Type.t
  | SurfacePattern of Surface_ast.Pattern.t

type import_result = {
  import_type : origin Macro_ast.typ_ option;
  import_expr : origin Macro_ast.exp_;
  import_type_var : Macro_ast.var;
  import_expr_var : Macro_ast.var;
}

type context = {
  resolve_embed_exn: string -> string;
  resolve_import_exn: string -> import_result;
}
