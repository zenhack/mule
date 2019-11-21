module type K = sig
  include Comparator.S

  val t_of_sexp : Sexp.t -> t
  val sexp_of_t : t -> Sexp.t
end

module MkMap(Key:K) = struct
  type 'a t = (Key.t, 'a, Key.comparator_witness) Map.t

  let t_of_sexp v_of_sexp m = Map.m__t_of_sexp (module Key) v_of_sexp m
  let sexp_of_t sexp_of_v m = Map.sexp_of_m__t (module Key) sexp_of_v m
end

module MkSet(Elt:K) = struct
  type t = (Elt.t, Elt.comparator_witness) Set.t

  let t_of_sexp s = Set.m__t_of_sexp (module Elt) s
  let sexp_of_t t = Set.sexp_of_m__t (module Elt) t
end
