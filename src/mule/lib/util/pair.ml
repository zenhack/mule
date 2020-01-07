module type Elt = sig
  include Comparable.S
  val sexp_of_t : t -> Sexp.t
  val t_of_sexp : Sexp.t -> t
end

module Make(Left:Elt)(Right:Elt) = struct
  module T = struct
    type t = (Left.t * Right.t)
    [@@deriving sexp, compare]
  end
  include T
  include Comparator.Make(T)
end
