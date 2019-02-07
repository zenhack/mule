(* Check for unbound variables. *)
val check_unbound : 'i Ast.Surface.Expr.t -> (Error.t, unit) OrErr.t
