type t

val equal : t -> t -> bool

val lca : t -> t -> t

val empty: t

val make_child : t -> t

val sexp_of_t : t -> Sexp.t
