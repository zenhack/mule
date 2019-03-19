open Common_ast

module RowMap = struct
  type 'v t = (Label.t, 'v, Label.comparator_witness) Map.t
end

module Type = struct
  type quantifier = [ `All | `Exist ]

  type 'i t =
    | Fn of ('i * 'i t * 'i t)
    | Recur of ('i * Var.t * 'i t)
    | Var of ('i * Var.t)
    | Record of ('i * (Label.t * 'i t) list * Var.t option)
    | Union of ('i * (Label.t * 'i t) list * Var.t option)
    | Quant of ('i * quantifier * Var.t * 'i t)
end

module Expr = struct
  type t =
    | Var of Var.t
    | Lam of (Var.t * t)
    | App of (t * t)
    | EmptyRecord
    | GetField of (t * Label.t)
    | Update of (t * Label.t * t)
    | Ctor of (Label.t * t)
    | Match of {
        cases: (Var.t * t) RowMap.t;
        default: (Var.t option * t) option;
      }
    | WithType of (t * unit Type.t)
    | Let of (Var.t * t * t)
end
