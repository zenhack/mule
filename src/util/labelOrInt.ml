module T = struct
  type t =
    | Label of Common_ast.Label.t
    | Int of int

  let compare l r = match (l, r) with
    | Label l', Label r' -> Common_ast.Label.compare l' r'
    | Int l', Int r' -> Int.compare l' r'
    | Label _, Int _ -> -1
    | Int _, Label _ -> 1

  let sexp_of_t = function
    | Label l ->
      Sexp.List [Sexp.Atom "label"; Common_ast.Label.sexp_of_t l]
    | Int n ->
      Sexp.List [Sexp.Atom "int"; Int.sexp_of_t n]
end
include T
include Comparator.Make(T)
