open Common_ast
module GT = Graph_types
module C = Constraint_t

type t

type 'a vtype

val make : Gensym.counter -> (t -> GT.g_node) -> t

val quant : GT.quant vtype
val typ : GT.typ vtype
val bound : GT.bound vtype
val kind : GT.kind vtype
val prekind : GT.prekind vtype
val guard : GT.guard vtype

val make_var : t -> 'a vtype -> 'a -> 'a GT.var
val read_var : t -> 'a vtype -> 'a GT.var -> 'a
val write_var : t -> 'a vtype -> 'a -> 'a GT.var -> unit

val var_eq : t -> 'a vtype -> 'a GT.var -> 'a GT.var -> bool

(* Merge (union) two variables. The last argument is the value of the resulting
   variable *)
val merge : t -> 'a vtype -> 'a GT.var -> 'a GT.var -> 'a -> unit

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

module DebugGraph : sig
  val dump : t -> unit
end
