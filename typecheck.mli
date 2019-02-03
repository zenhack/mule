include module type of Typecheck_t

val typecheck : 'i Ast.Expr.t -> ('i error, unit Ast.Type.t) OrErr.t
