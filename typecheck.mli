include module type of Typecheck_t

val typecheck : 'i Ast.Expr.t -> ('i error, int Ast.Type.t) OrErr.t
