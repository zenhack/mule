

type t =
  [ `Relative of string
  | `Absolute of string
  ]
[@@deriving sexp_of]
