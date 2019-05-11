open Common_ast

module Expr = struct
  type t =
    | Var of int
    | Fix of [ `Let | `Record ]
    | Lam of (int * t list * t)
    | App of (t * t)
    | Record of t LabelMap.t
    | GetField of ([`Lazy|`Strict] * Label.t)
    | Update of
        { old: t
        ; label: Label.t
        ; field: t
        }
    | Ctor of (Label.t * t)
    | Match of {
        cases: t LabelMap.t;
        default: t option;
      }
    | Lazy of (t list * t ref)
    | Vec of t array
    | Integer of Z.t
end
