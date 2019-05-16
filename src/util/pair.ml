module type Elt = sig
  include Comparable.S
  val sexp_of_t : t -> Sexp.t
end

module type Pair = sig
  module Left : Elt
  module Right : Elt
end

module Make(P:Pair) = struct
  module T = struct
    type t = (P.Left.t * P.Right.t)

    let sexp_of_t (l, r) =
      Sexp.List
        [ P.Left.sexp_of_t l
        ; P.Right.sexp_of_t r
        ]

    let compare (x1, y1) (x2, y2) =
      let r = P.Left.compare x1 x2 in
      if r = 0 then
        P.Right.compare y1 y2
      else
        r
  end
  include T
  include Comparator.Make(T)
end
