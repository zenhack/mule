module Make(Left:Elt.S)(Right:Elt.S) = struct
  module T = struct
    type t = (Left.t * Right.t)

    let sexp_of_t (l, r) =
      Sexp.List [
        Left.sexp_of_t l;
        Right.sexp_of_t r;
      ]

    let t_of_sexp = function
      | Sexp.List [l; r] ->
          ( Left.t_of_sexp l
          , Right.t_of_sexp r
          )
      | sexp ->
          raise (Sexp.Of_sexp_error (Failure "t_of_sexp: pair needed", sexp))


    let compare (x1, y1) (x2, y2) =
      let r = Left.compare x1 x2 in
      if r = 0 then
        Right.compare y1 y2
      else
        r
  end
  include T
  include Comparator.Make(T)
end
