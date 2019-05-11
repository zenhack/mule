open Common_ast

module Kind = struct
  type t =
    | Unknown
    | Type
    | Row
end

module Type = struct
  type quantifier = [ `All | `Exist ]

  type 'i t =
    | Fn of ('i * 'i t * 'i t)
    | Recur of ('i * Var.t * 'i t)
    | Var of ('i * Var.t)
    | Record of 'i row
    | Union of 'i row
    | Quant of ('i * quantifier * Var.t * Kind.t * 'i t)
  and 'i row =
    ('i * (Label.t * 'i t) list * Var.t option)

  let rec map ty ~f = match ty with
    | Fn(x, l, r) ->
        Fn(f x, map l ~f, map r ~f)
    | Recur(x, v, body) ->
        Recur(f x, v, map body ~f)
    | Var (x, v) ->
        Var(f x, v)
    | Record row ->
        Record(map_row row ~f)
    | Union row ->
        Union(map_row row ~f)
    | Quant(x, q, v, k, body) ->
        Quant(f x, q, v, k, map body ~f)
  and map_row (x, fields, rest) ~f =
    ( f x
    , List.map fields ~f:(fun(l, t) -> (l, map t ~f))
    , rest
    )
end

module Expr = struct
  type t =
    | Var of Var.t
    | Lam of (Var.t * t)
    | App of (t * t)
    | Fix of [ `Let | `Record ]
    | EmptyRecord
    | GetField of ([`Lazy|`Strict] * Label.t)
    | Update of Label.t
    | Ctor of (Label.t * t)
    | Match of {
        cases: (Var.t * t) LabelMap.t;
        default: (Var.t option * t) option;
      }
    | WithType of unit Type.t
    | Let of (Var.t * t * t)
    | Integer of Z.t
end
