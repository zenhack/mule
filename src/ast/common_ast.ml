type var = Var of string

module Label : sig
  type t

  val of_string : string -> t
  val to_string : t -> string

  val compare : t -> t -> int
end = struct
  type t = Label of string

  let of_string s = Label s
  let to_string (Label s) = s

  let compare (Label l) (Label r) = String.compare l r
end
