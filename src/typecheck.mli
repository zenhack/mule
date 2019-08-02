val typecheck
  : 'i Ast.Desugared.Expr.t
  -> (int Ast.Desugared.Type.t, MuleErr.t) Result.t
