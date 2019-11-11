module Make(E:Elt.S) = struct
  module T = struct
    type t = E.t list

    let sexp_of_t lst =
      Sexp.List (List.map lst ~f:E.sexp_of_t)

    let t_of_sexp = function
      | Sexp.List ls ->
          List.map ls ~f:E.t_of_sexp
      | sexp ->
          raise (Sexp.Of_sexp_error (Failure "t_of_sexp: list needed", sexp))


    let rec compare xs ys = match (xs, ys) with
      | [], [] -> 0
      | (_::_), [] -> 1
      | [], (_::_) -> -1
      | (x::xs), (y::ys) ->
          let r = E.compare x y in
          if r = 0 then
            compare xs ys
          else
            r
  end
  include T
  include Comparator.Make(T)
end
