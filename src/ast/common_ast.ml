open Base

module type StringWrapper_S = sig
  include Comparator.S

  val compare : t -> t -> int
  val sexp_of_t : t -> Sexp.t

  val of_string : string -> t
  val to_string : t -> string

  val equal : t -> t -> bool
end

module StringWrapper : StringWrapper_S = struct
  module T = struct
    type t = string
    let sexp_of_t = sexp_of_string
    let compare = String.compare
  end

  include T
  include Comparator.Make(T)

  let of_string s = s
  let to_string s = s


  let equal = String.equal
end

module Var : StringWrapper_S = StringWrapper
module Label : StringWrapper_S = StringWrapper
