type maybe_kind =
  [ `Unknown
  | `Type
  | `Row
  | `Arrow of maybe_kind * maybe_kind
  ]
[@@deriving sexp_of]

type t =
  [ `Type
  | `Row
  | `Arrow of t * t
  ]
[@@deriving sexp_of]
