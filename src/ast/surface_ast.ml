open Common_ast

module Type = struct
  type t =
    | Fn of (t * t)
    | All of (Var.t list * t)
    | Recur of (Var.t * t)
    | Var of Var.t
    | Record of (record_item list)
    | Ctor of Label.t
    | App of (t * t)
    | Union of (t * t)
    | RowRest of Var.t
  and record_item =
    | Field of (Label.t * t)
    | Rest of Var.t
end

module Pattern = struct
  type t =
    | Ctor of (Label.t * t)
    | Var of Var.t
    | Wild
    | Annotated of (t * Type.t)
end

module Expr = struct
  type t =
    | App of (t * t)
    | Lam of (Pattern.t list * t)
    | Var of Var.t
    | Record of (Label.t * t) list
    | GetField of (t * Label.t)
    | Ctor of Label.t
    | Update of (t * (Label.t * t) list)
    | Match of (t * (Pattern.t * t) list)
    | Let of (Pattern.t * t * t)
end
