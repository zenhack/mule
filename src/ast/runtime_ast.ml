open Common_ast

module Expr = struct
  type 'a io = unit -> 'a Lwt.t

  let sexp_of_io _ _ = sexp_of_string "<io>"

  type t =
    | Var of int
    | Lam of (int * t list * t)
    | LetRec of ((int * t) list * t)
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
    | ConstMatch of
        { cm_cases: t ConstMap.t
        ; cm_default: t
        }
    | Lazy of (t list * t ref)
    | Vec of t array
    | Const of Const.t
    | Prim of (t -> t)
    | PrimIO of (t io)
  [@@deriving sexp_of]
end
