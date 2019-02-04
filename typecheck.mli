include module type of Typecheck_t

val typecheck : 'i Ast.Surface.Expr.t -> ('i error, int Ast.Surface.Type.t) OrErr.t
