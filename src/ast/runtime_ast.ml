open Common_ast

type 'a rowmap = (Label.t, 'a, Label.comparator_witness) Map.t

module Expr = struct
  type t =
    | Var of Var.t
    | Lam of (Var.t * t)
    | App of (t * t)
    | Record of t rowmap
    | GetField of Label.t
    | Update of
        { old: t
        ; label: Label.t
        ; field: t
        }
    | Ctor of (Label.t * t)
    | Match of {
        cases: t rowmap;
        default: t option;
      }
end
