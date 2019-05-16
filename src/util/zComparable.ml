module T = struct
  type t = Z.t

  let compare = Z.compare
  let sexp_of_t t = Sexp.Atom (Z.to_string t)
end
include T
include Comparator.Make(T)
