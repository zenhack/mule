module T = struct
  type t = (int * int)
  let compare (lx, ly) (rx, ry) =
    match Int.compare lx rx with
      | 0 -> Int.compare ly ry
      | result -> result
  let sexp_of_t (x, y) =
    sexp_of_list sexp_of_int [x; y]
end
include T
include Comparator.Make(T)
