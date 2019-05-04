open Common_ast

module Expr = struct
  type t =
    | Var of int
    | Lam of (int * t list * t)
    | App of (t * t)
    | Record of t LabelMap.t
    | GetField of Label.t
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
    | Lazy of t ref
    | LetRec of (t list * t)
    | Vec of t array
end
