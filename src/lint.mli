(** Run several ad-hoc static checks on an expression:
  *
  * - make sure there are no expressions with duplicate record fields.
  * - check for unbound variables.
  *
  * This is invoked by the type checker, before doing the more principled
  * hindley-milner type inference algorithm.
  *)
val check : Ast.Surface.Expr.t -> (MuleErr.t, unit) OrErr.t
