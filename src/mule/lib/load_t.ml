type result = {
  typ: int Desugared_ast_type_t.t;
  typ_var: Typecheck_types_t.u_var;
  rt_expr: Runtime_ast.Expr.t Lazy.t;
  js_expr: Js_ast_t.expr Lazy.t;
  var : Common_ast.Var.t;
}
