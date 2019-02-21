open Common_ast

module RowMap = Map.Make(Label)

module Type = struct
  type 'i mono =
    | Fn of ('i * 'i mono * 'i mono)
    | Recur of ('i * Var.t * 'i mono)
    | Var of ('i * Var.t)
    | Record of ('i * (Label.t * 'i mono) list * Var.t option)
    | Union of ('i * (Label.t * 'i mono) list * Var.t option)
  and 'i poly =
    | Bottom
    | All of ('i prefix * 'i mono)
  and 'i prefix
    = (Var.t * 'i bound) list
  and 'i bound =
    | Flex of ('i poly)
    | Rigid of ('i poly)
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
end
