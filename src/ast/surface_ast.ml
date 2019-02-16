open Sexplib.Std
open Common_ast

module Type = struct
  type t =
    | Fn of (t * t)
    | Recur of (Var.t * t)
    | Var of Var.t
    | Record of ((Label.t * t) list * Var.t option)
    | Union of ((Label.t * t) list * Var.t option)
    [@@deriving sexp]
end

module Pattern = struct
  type t =
    | Ctor of (Label.t * t)
    | Var of Var.t
    | Wild
    | Annotated of (t * Type.t)
    [@@deriving sexp]
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
    [@@deriving sexp]
end
