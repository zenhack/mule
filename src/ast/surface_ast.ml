open Sexplib.Std
open Common_ast

module Type = struct
  type 'i t =
    | Fn of ('i * 'i t * 'i t)
    | Recur of ('i * Var.t * 'i t)
    | Var of ('i * Var.t)
    | Record of ('i * (Label.t * 'i t) list * Var.t option)
    | Union of ('i * (Label.t * 'i t) list * Var.t option)
    [@@deriving sexp]

  let get_info = function
    | Fn(i, _, _) -> i
    | Recur(i, _, _) -> i
    | Var(i, _) -> i
    | Record(i, _, _) -> i
    | Union(i, _, _) -> i
end

module Pattern = struct
  type t =
    | Ctor of (Label.t * t)
    | Var of Var.t
    | Wild
    | Annotated of (t * unit Type.t)
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
