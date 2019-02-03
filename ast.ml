

type var = Var of string

type label = Label of string

module Expr = struct
  type 'i t =
    | App of ('i * 'i t * 'i t)
    | Lam of ('i * var * 'i t)
    | Var of ('i * var)
    | Record of ('i * (label * 'i t) list)

  let rec map_info f = function
    | App (i, l, r) -> App (f i, map_info f l, map_info f r)
    | Lam (i, param, body) -> Lam (f i, param, map_info f body)
    | Var (i, v) -> Var (f i, v)
    | Record (i, fields) ->
        let new_fields = List.map (fun (l, v) -> (l, map_info f v)) fields in
        Record (f i, new_fields)
end

module Type = struct
  type 'i t =
    | Fn of ('i * 'i t * 'i t)
    | Recur of ('i * var * 'i t)
    | Var of ('i * var)

  let get_info = function
    | Fn(i, _, _) -> i
    | Recur(i, _, _) -> i
    | Var(i, _) -> i
end
