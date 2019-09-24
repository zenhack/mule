open Common_ast

module T = struct
  type t = {
    p_var: Var.t;
    p_lbls: Label.t list;
  }

  let sexp_of_t p =
    Sexp.List
      ( Var.sexp_of_t p.p_var
        :: List.map p.p_lbls ~f:Label.sexp_of_t
      )

  let t_of_sexp = function
    | Sexp.List (s :: ss) -> {
        p_var = Var.t_of_sexp s;
        p_lbls = List.map ss ~f:Label.t_of_sexp;
      }
    | sexp ->
        raise (Sexp.Of_sexp_error (Failure "t_of_sexp: non-empty list needed", sexp))

  let compare l r =
    match Var.compare l.p_var r.p_var with
    | 0 -> LabelList.compare l.p_lbls r.p_lbls
    | res -> res

end

include T
include Comparator.Make(T)
