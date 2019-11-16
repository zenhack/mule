type result = {
  typ: int Desugared_ast_type_t.t;
  rt_expr: Runtime_ast.Expr.t Lazy.t;
  js_expr: Js_ast_t.expr Lazy.t;
}
