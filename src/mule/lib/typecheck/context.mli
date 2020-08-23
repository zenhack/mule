open Common_ast
module GT = Graph_types
module C = Constraint_t

type t

val make : Gensym.counter -> (t -> GT.g_node) -> t

val make_quant : t -> GT.quant -> GT.quant GT.var
val make_type : t -> GT.typ -> GT.typ GT.var
val make_bound : t -> GT.bound -> GT.bound GT.var

val make_kind : t -> GT.kind -> GT.kind GT.var
val make_prekind : t -> GT.prekind -> GT.prekind GT.var
val make_guard : t -> GT.guard -> GT.guard GT.var

val with_quant : t -> GT.bound -> (GT.quant GT.var -> GT.typ GT.var) -> GT.quant GT.var
val with_sub_g : t -> (t -> GT.g_node -> GT.quant GT.var) -> GT.g_node

val get_g : t -> GT.g_node

val with_val_binding : t -> Var.t -> C.val_var -> (t -> 'a) -> 'a
val lookup_val : t -> Var.t -> C.val_var option

val with_type_binding : t -> Var.t -> C.type_var -> (t -> 'a) -> 'a
val lookup_type : t -> Var.t -> C.type_var option

val get_ctr : t -> Gensym.counter

val constrain : t -> C.constr -> unit

val get_constraints : t -> C.constr list

(* Make an independent copy of the context *)
val checkpoint : t -> t
