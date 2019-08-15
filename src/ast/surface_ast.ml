open Common_ast

module Located : sig
  type point = (int * int * int)
  type range
  type 'a t

  val sexp_of_point : point -> Sexp.t
  val point_of_sexp : Sexp.t -> point
  val sexp_of_range : range -> Sexp.t
  val range_of_sexp : Sexp.t -> range
  val sexp_of_t : ('a -> Sexp.t) -> 'a t -> Sexp.t
  val t_of_sexp : (Sexp.t -> 'a) -> Sexp.t -> 'a t

  val value : 'a t -> 'a
  val loc : 'a t -> range
  val start : range -> point
  val stop : range -> point

  val mk_range : point -> point -> range

  val at : range -> 'a -> 'a t
  val spaning : 'a t -> 'b t -> 'c -> 'c t
end = struct
  (* This is the same as [MParser.pos] but by inlining it
   * we can derive sexp. *)
  type point = (int * int * int)
  [@@deriving sexp]

  (* (start, end) *)
  type range = (point * point)
  [@@deriving sexp]

  type 'a t = (range * 'a)
  [@@deriving sexp]

  let value: 'a t -> 'a = snd
  let loc: 'a t -> range = fst

  let start: range -> point = fst
  let stop: range -> point = snd

  let mk_range start stop = (start, stop)

  let at loc x = (loc, x)

  let spaning: 'a t -> 'b t -> 'c -> 'c t =
    fun l r v -> ((start (loc l), stop (loc r)), v)
end

module L = Located

module Type = struct
  type quantifier = [ `All | `Exist ]
  [@@deriving sexp]

  type t =
    | Fn of (t L.t * t L.t)
    | Quant of (quantifier L.t * Var.t L.t list * t L.t)
    | Recur of (Var.t L.t * t L.t)
    | Var of Var.t
    | Record of (record_item L.t list)
    | Ctor of Label.t
    | App of (t L.t * t L.t)
    | Union of (t L.t * t L.t)
    | RowRest of Var.t
    | Annotated of (Var.t L.t * t L.t)
    | Path of (Var.t L.t * Label.t L.t list)
  [@@deriving sexp]

  and record_item =
    | Field of (Label.t L.t * t L.t)
    | Type of (Label.t L.t * Var.t L.t list * t L.t option)
    | Rest of Var.t
  [@@deriving sexp]
end

module Pattern = struct
  type t =
    | Ctor of (Label.t L.t * t L.t)
    | Var of (Var.t L.t * Type.t L.t option)
    | Wild
    | Const of Const.t
  [@@deriving sexp]
end

module Expr = struct
  type t =
    | App of (t L.t * t L.t)
    | Lam of (Pattern.t L.t list * t L.t)
    | Var of Var.t
    | Record of field L.t list
    | GetField of (t L.t * Label.t L.t)
    | Ctor of Label.t
    | Update of (t L.t * field L.t list)
    | Match of (t L.t * (Pattern.t L.t * t L.t) L.t list)
    | Let of (binding L.t list * t L.t)
    | WithType of (t L.t * Type.t L.t)
    | Const of Const.t
  [@@deriving sexp]
  and binding =
    [ `BindType of Var.t L.t * Var.t L.t list * Type.t L.t
    | `BindVal of Pattern.t L.t * t L.t
    ]
  [@@deriving sexp]
  and field =
    [ `Value of
        ( Label.t L.t
          * Type.t L.t option
          * t L.t
        )
    | `Type of (Label.t L.t * Var.t L.t list * Type.t L.t)
    ]
  [@@deriving sexp]
end
