open Sexplib.Std
module Sexp = Sexplib.Sexp
open Common_ast

module RowMap : sig
  include module type of Map.Make(Label)
  val sexp_of_t : ('a -> Sexp.t) -> 'a t -> Sexp.t
end = struct
  include Map.Make(Label)

  type 'a binding = (Label.t * 'a)
  [@@deriving sexp_of]

  let sexp_of_t sexp_of_val map =
    bindings map
    |> sexp_of_list (sexp_of_binding sexp_of_val)
end

module Type = struct
  type 'i mono =
    | Fn of ('i * 'i mono * 'i mono)
    | Recur of ('i * Var.t * 'i mono)
    | Var of ('i * Var.t)
    | Record of ('i * (Label.t * 'i mono) list * Var.t option)
    | Union of ('i * (Label.t * 'i mono) list * Var.t option)
    [@@deriving sexp]
  and 'i poly =
    | Bottom of 'i
    | All of ('i * 'i prefix * 'i mono)
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
    [@@deriving sexp_of]
end
