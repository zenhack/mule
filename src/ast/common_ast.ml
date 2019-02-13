open Sexplib.Std
module Sexp = Sexplib.Sexp

module StringWrapper : sig
  type t

  val of_string : string -> t
  val to_string : t -> string

  val sexp_of_t : t -> Sexp.t
  val t_of_sexp : Sexp.t -> t

  val compare : t -> t -> int
end = struct
  type t = string [@@deriving sexp]

  let of_string s = s
  let to_string s = s

  let compare = String.compare
end

module Var : module type of StringWrapper = StringWrapper
module Label : module type of StringWrapper = StringWrapper
