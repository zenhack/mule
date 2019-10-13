include module type of To_macro_t

val expr_exn : context -> Surface_ast.Expr.t -> origin Macro_ast.exp_
val typ_exn : context -> Surface_ast.Type.t -> origin Macro_ast.typ_
