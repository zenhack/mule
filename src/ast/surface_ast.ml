open Sexplib.Std
open Common_ast

module Pattern = struct
  type 'i t =
    | Ctor of ('i * Label.t * 'i t)
    | Var of ('i * var)
    | Wild of 'i
    [@@deriving sexp]

  let rec map_info f = function
    | Ctor (i, lbl, p) ->
        Ctor (f i, lbl, map_info f p)
    | Var (i, v) ->
        Var (f i, v)
    | Wild i -> Wild (f i)
end

module Expr = struct
  type 'i t =
    | App of ('i * 'i t * 'i t)
    | Lam of ('i * ('i Pattern.t) list * 'i t)
    | Var of ('i * var)
    | Record of ('i * (Label.t * 'i t) list)
    | GetField of ('i * 'i t * Label.t)
    | Ctor of ('i * Label.t)
    | Update of ('i * 'i t * (Label.t* 'i t) list)
    | Match of ('i * 'i t * ('i Pattern.t * 'i t) list)
    [@@deriving sexp]

  let rec map_info f = function
    | App (i, l, r) -> App (f i, map_info f l, map_info f r)
    | Lam (i, params, body) ->
        Lam
          ( f i
          , List.map (Pattern.map_info f) params
          , map_info f body
          )
    | Var (i, v) -> Var (f i, v)
    | Record (i, fields) ->
        let new_fields = List.map (fun (l, v) -> (l, map_info f v)) fields in
        Record (f i, new_fields)
    | GetField (i, e, lbl) ->
        GetField(f i, map_info f e, lbl)
    | Ctor (i, l) -> Ctor (f i, l)
    | Update (i, r, updates) ->
        Update
          ( f i
          , map_info f r
          , List.map (fun (l, e) -> (l, map_info f e)) updates
          )
    | Match (i, e, cases) ->
        Match
          ( f i
          , map_info f e
          , List.map (fun (p, v) -> (Pattern.map_info f p, map_info f v)) cases
          )
end

module Type = struct
  type 'i t =
    | Fn of ('i * 'i t * 'i t)
    | Recur of ('i * var * 'i t)
    | Var of ('i * var)
    | Record of ('i * (Label.t * 'i t) list * var option)
    | Union of ('i * (Label.t * 'i t) list * var option)
    [@@deriving sexp]

  let get_info = function
    | Fn(i, _, _) -> i
    | Recur(i, _, _) -> i
    | Var(i, _) -> i
    | Record(i, _, _) -> i
    | Union(i, _, _) -> i
end
