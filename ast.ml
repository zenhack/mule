

type var = Var of string

module Expr = struct
  type 'i t =
    | App of ('i * 'i t * 'i t)
    | Lam of ('i * var * 'i t)
    | Var of ('i * var)

  let rec map_info f = function
    | App (i, l, r) -> App (f i, map_info f l, map_info f r)
    | Lam (i, param, body) -> Lam (f i, param, map_info f body)
    | Var (i, v) -> Var (f i, v)
end

module Type = struct
  type 'i t =
    | Fn of ('i * 'i t * 'i t)
    | Rec of ('i * var * 'i t)
    | Var of ('i * var)
end
