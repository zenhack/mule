open Common_ast

module Kind = struct
  type maybe_kind =
    [ `Unknown
    | `Type
    | `Row
    | `Arrow of maybe_kind * maybe_kind
    ]
  [@@deriving sexp]

  type t =
    [ `Type
    | `Row
    | `Arrow of t * t
    ]
  [@@deriving sexp]

  let rec default_unknowns = function
    | `Unknown -> `Type
    | `Row -> `Row
    | `Type -> `Type
    | `Arrow(x, y) -> `Arrow(default_unknowns x, default_unknowns y)
end

module Type = struct
  type quantifier = [ `All | `Exist ]
  [@@deriving sexp]

  type 'i t =
    | Fn of ('i * 'i t * 'i t)
    | Recur of ('i * Var.t * 'i t)
    | Var of ('i * Var.t)
    | Path of ('i * Var.t * Label.t list)
    | Record of
        { r_info : 'i
        ; r_types : 'i row
        ; r_values : 'i row
        }
    | Union of 'i row
    | Quant of ('i * quantifier * Var.t * Kind.maybe_kind * 'i t)
    | Named of ('i * string)
    | Opaque of ('i * Kind.maybe_kind)
    | Annotated of ('i * Var.t * 'i t)
    | TypeLam of ('i * Var.t * 'i t)
    | App of ('i * 'i t * 'i t)
  [@@deriving sexp]
  and 'i row =
    ('i * (Label.t * 'i t) list * Var.t option)
  [@@deriving sexp]

  let get_info = function
    | Fn(x, _, _) -> x
    | Recur(x, _, _) -> x
    | Var(x, _) -> x
    | Path(x, _, _) -> x
    | Record {r_info; _} -> r_info
    | Union(x, _, _) -> x
    | Quant(x, _, _, _, _) -> x
    | Named(x, _) -> x
    | Opaque (x, _) -> x
    | Annotated(x, _, _) -> x
    | TypeLam(x, _, _) -> x
    | App(x, _, _) -> x

  let rec map ty ~f = match ty with
    | Annotated(x, v, t) -> Annotated(f x, v, map t ~f)
    | Opaque (x, k) -> Opaque (f x, k)
    | Named(x, s) ->
        Named(f x, s)
    | Fn(x, l, r) ->
        Fn(f x, map l ~f, map r ~f)
    | Recur(x, v, body) ->
        Recur(f x, v, map body ~f)
    | Path(x, v, ls) ->
        Path(f x, v, ls)
    | Var (x, v) ->
        Var(f x, v)
    | Record {r_info; r_types; r_values} ->
        Record
          { r_info = f r_info
          ; r_types = map_row r_types ~f
          ; r_values = map_row r_values ~f
          }
    | Union row ->
        Union(map_row row ~f)
    | Quant(x, q, v, k, body) ->
        Quant(f x, q, v, k, map body ~f)
    | TypeLam(x, v, body) ->
        TypeLam(f x, v, map body ~f)
    | App(x, fn, arg) ->
        App(f x, map fn ~f, map arg ~f)
  and map_row (x, fields, rest) ~f =
    ( f x
    , List.map fields ~f:(fun(l, t) -> (l, map t ~f))
    , rest
    )
end

module Expr = struct
  type 'i t =
    | Var of Var.t
    | Lam of (Var.t * 'i t)
    | App of ('i t * 'i t)
    | Fix of [ `Let | `Record ]
    | EmptyRecord
    | GetField of ([`Lazy|`Strict] * Label.t)
    | Update of ([`Value | `Type] * Label.t)
    | Ctor of (Label.t * 'i t)
    | Match of {
        cases: (Var.t * 'i t) LabelMap.t;
        default: (Var.t option * 'i t) option;
      }
    | IntMatch of
        { im_cases : 'i t ZMap.t
        ; im_default: 'i t
        }
    | WithType of 'i Type.t
    | Witness of 'i Type.t
    | Let of (Var.t * 'i t * 'i t)
    | LetType of ((Var.t * 'i Type.t) list * 'i t)
    | Integer of Bigint.t
    | Text of string
  [@@deriving sexp]

  let apply_to_kids e ~f = match e with
    | Lam (v, body) -> Lam (v, f body)
    | App(x, y) -> App(f x, f y)
    | Ctor(l, arg) -> Ctor(l, f arg)
    | Match {cases; default} ->
        Match
          { cases = Map.map cases ~f:(fun (k, v) -> (k, f v))
          ; default = Option.map default ~f:(fun (k, v) -> (k, f v))
          }
    | IntMatch {im_cases; im_default} ->
        IntMatch
          { im_cases = Map.map im_cases ~f
          ; im_default = f im_default
          }
    | Let(v, e, body) -> Let(v, f e, f body)
    | LetType(binds, body) -> LetType(binds, f body)
    | Var _
    | Fix _
    | EmptyRecord
    | GetField _
    | Update _
    | WithType _
    | Witness _
    | Integer _
    | Text _ -> e
end
