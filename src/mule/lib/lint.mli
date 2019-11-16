(** Run several ad-hoc static checks on an expression:
  *
  * - make sure there are no expressions with duplicate record fields.
  * - check for unbound variables.
  *
  * This is invoked by the type checker, before doing the more principled
  * type inference algorithm.
*)
val check_expr : Surface_ast.Expr.lt -> unit

(* Same thing, but for types: *)
val check_type : Surface_ast.Type.lt -> unit
