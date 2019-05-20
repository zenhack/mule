module T = struct
  include Z

  let sexp_of_t n = sexp_of_string (Z.to_string n)
  let t_of_sexp s = Z.of_string (string_of_sexp s)
end

include T
include Comparator.Make(T)
