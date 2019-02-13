open Sexplib.Std
module Sexp = Sexplib.Sexp

type var =
  Var of string
  [@@deriving sexp]

module Label : sig
  type t

  val of_string : string -> t
  val to_string : t -> string

  val compare : t -> t -> int

  val sexp_of_t : t -> Sexp.t
  val t_of_sexp : Sexp.t -> t
end = struct

  type t = string [@@deriving sexp]

  let of_string s = s
  let to_string s = s

  let compare = String.compare
end
