
open Typecheck_types
open Common_ast

type t

type row = (Label.t * t) list * t option

val build : sign -> bound_target -> t -> u_var
val at_g : g_node -> t -> u_var

val all : k_var -> (t -> t) -> t
val exist : k_var -> (t -> t) -> t

val ( **> ) : t -> t -> t
val record : row -> row -> t
val record_v : row -> t
val record_t : row -> t
val union : row -> t

val int : t
val text : t
val char : t

val witness : t -> t

val return : u_var -> t
