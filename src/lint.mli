(** Run several ad-hoc static checks on an expression:
  *
  * - make sure there are no expressions with duplicate record fields.
  * - check for unbound variables.
  *
  * This is invoked by the type checker, before doing the more principled
  * type inference algorithm.
  *)
val check : Ast.Surface.Expr.t -> (unit, MuleErr.t) Result.t
