module StringWrapper : sig
  type t

  val of_string : string -> t
  val to_string : t -> string

  val compare : t -> t -> int

  val equal : t -> t -> bool
end = struct
  type t = string

  let of_string s = s
  let to_string s = s

  let compare = String.compare

  let equal = String.equal
end

module Var : module type of StringWrapper = StringWrapper
module Label : module type of StringWrapper = StringWrapper
