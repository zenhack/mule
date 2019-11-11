module type S = sig
  include Comparable.S
  val sexp_of_t : t -> Sexp.t
  val t_of_sexp : Sexp.t -> t
end
