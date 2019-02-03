

type var = Var of string

module Expr = struct
  type 'i t =
    | App of ('i * 'i t * 'i t)
    | Lam of ('i * var * 'i t)
    | Var of ('i * var)
end

module Type = struct
  type 'i t =
    | Fn of ('i * 'i t * 'i t)
    | Rec of ('i * var * 'i t)
    | Var of ('i * var)
end
