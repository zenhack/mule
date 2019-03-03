open Common_ast

module RowMap = Map.Make(Label)

module Type = struct
  type 'i t =
    | Fn of ('i * 'i t * 'i t)
    | Recur of ('i * Var.t * 'i t)
    | Var of ('i * Var.t)
    | Record of ('i * (Label.t * 'i t) list * Var.t option)
    | Union of ('i * (Label.t * 'i t) list * Var.t option)
    | All of ('i * Var.t * 'i t)
end

module Expr = struct
  type t =
    | Var of Var.t
    | Lam of (Var.t * t)
    | App of (t * t)
    | Record of t RowMap.t
    | GetField of (t * Label.t)
    | Update of (t * (Label.t * t) list)
    | Ctor of (Label.t * t)
    | Match of {
        cases: (Var.t * t) RowMap.t;
        default: (Var.t option * t) option;
      }
    | WithType of (t * unit Type.t)
    | Let of (Var.t * t * t)
end
