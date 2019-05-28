open Common_ast

module Type = struct
  type quantifier = [ `All | `Exist ]
  [@@deriving sexp]

  type t =
    | Fn of (t * t)
    | Quant of (quantifier * Var.t list * t)
    | Recur of (Var.t * t)
    | Var of Var.t
    | Record of (record_item list)
    | Ctor of Label.t
    | App of (t * t)
    | Union of (t * t)
    | RowRest of Var.t
  [@@deriving sexp]
and record_item =
  | Field of (Label.t * t)
  | Type of (Label.t * t option)
  | Rest of Var.t
[@@deriving sexp]
end

module Pattern = struct
  type t =
    | Ctor of (Label.t * t)
    | Var of Var.t
    | Wild
    | Annotated of (t * Type.t)
    | Integer of Bigint.t
  [@@deriving sexp]
end

module Expr = struct
  type t =
    | App of (t * t)
    | Lam of (Pattern.t list * t)
    | Var of Var.t
    | Record of field list
    | GetField of (t * Label.t)
    | Ctor of Label.t
    | Update of (t * field list)
    | Match of (t * (Pattern.t * t) list)
    | Let of (Pattern.t * t * t)
    | WithType of (t * Type.t)
    | Integer of Bigint.t
  [@@deriving sexp]
and field =
  [ `Value of
      ( Label.t
        * Type.t option
        * t
      )
  | `Type of (Label.t * Type.t)
  ]
[@@deriving sexp]
end
