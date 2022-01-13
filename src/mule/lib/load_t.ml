module GT = Graph_types

type result = {
  typ: unit Desugared_ast_type_t.t;
  typ_var: GT.quant GT.var;
  rt_expr: Runtime_ast.Expr.t Lazy.t;
  js_expr: Js_ast_t.expr Lazy.t;
  var : Common_ast.Var.t;
}
