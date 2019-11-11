
(* Generate a unique integer, greater than all previously generated
 * integers. *)
val gensym : unit -> int

(* Generate an anonymous variable name -- guaranteed not to clash with
 * any user-named variables, nor any other anonymous variables. *)
val anon_var : unit -> Common_ast.Var.t
