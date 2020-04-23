
type counter

val global : counter

(* Generate a unique integer, greater than all previously generated
 * integers. *)
val gensym : counter -> int

(* Generate an anonymous variable name -- guaranteed not to clash with
 * any user-named variables, nor any other anonymous variables. *)
val anon_var : counter -> Common_ast.Var.t
