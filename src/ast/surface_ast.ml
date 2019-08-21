open Common_ast

module Type = struct
  type quantifier = [ `All | `Exist ]
  [@@deriving sexp_of]

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
    | Annotated of (Var.t * t)
    | Path of (Var.t * Label.t list)
    | Import of string
  [@@deriving sexp_of]

  and record_item =
    | Field of (Label.t * t)
    | Type of (Label.t * Var.t list * t option)
    | Rest of Var.t
  [@@deriving sexp_of]
end

module Pattern = struct
  type t =
    | Ctor of (Label.t * t)
    | Var of (Var.t * Type.t option)
    | Wild
    | Const of Const.t
  [@@deriving sexp_of]
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
    | Let of (binding list * t)
    | WithType of (t * Type.t)
    | Const of Const.t
    | Import of
        { i_path : string
        ; i_loc : Loc.t
        }
    | Embed of string
  [@@deriving sexp_of]
  and binding =
    [ `BindType of Var.t * Var.t list * Type.t
    | `BindVal of Pattern.t * t
    ]
  [@@deriving sexp_of]
  and field =
    [ `Value of
        ( Label.t
          * Type.t option
          * t
        )
    | `Type of (Label.t * Var.t list * Type.t)
    ]
  [@@deriving sexp_of]
end
