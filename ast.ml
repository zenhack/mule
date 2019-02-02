

type var = Var of string

type 'i expr =
  | EApp of ('i * 'i expr * 'i expr)
  | ELam of ('i * var * 'i expr)
  | EVar of ('i * var)
