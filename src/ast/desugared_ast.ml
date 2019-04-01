open Common_ast


module Type = struct
  type quantifier = [ `All | `Exist ]

  type 'i t =
    | Fn of ('i * 'i t * 'i t)
    | Recur of ('i * Var.t * 'i t)
    | Var of ('i * Var.t)
    | Record of 'i row
    | Union of 'i row
    | Quant of ('i * quantifier * Var.t * 'i t)
  and 'i row =
    ('i * (Label.t * 'i t) list * Var.t option)
end

module Expr = struct
  type t =
    | Var of Var.t
    | Lam of (Var.t * t)
    | App of (t * t)
    | EmptyRecord
    | GetField of Label.t
    | Update of Label.t
    | Ctor of (Label.t * t)
    | Match of {
        cases: (Var.t * t) LabelMap.t;
        default: (Var.t option * t) option;
      }
    | WithType of (t * unit Type.t)
    | Let of (Var.t * t * t)
end
