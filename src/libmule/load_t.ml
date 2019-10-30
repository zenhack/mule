
type entry = {
  surface        : Surface_ast.Module.t;
  desugared_val  : Desugared_ast_kind.maybe_kind Desugared_ast_expr.t;
  desugared_type : Desugared_ast_kind.maybe_kind Desugared_ast_type.t;
  solver_type    : Typecheck_types_t.u_var;
  runtime_expr   : Runtime_ast.Expr.t Lazy.t;
}
