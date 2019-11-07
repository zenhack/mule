
open Common_ast

type u_kind =
  [ `Free of int
  | `Row
  | `Type
  | `Arrow of k_var * k_var
  ]
and k_var = u_kind UnionFind.var

type typeconst_name =
  [ `Text
  | `Int
  | `Char
  | `Fn
  | `Record
  | `Union
  | `Apply
  | `Lambda
  ]

type u_typeconst =
  [ `Named of typeconst_name
  | `Extend of Label.t
  ]
(* Contents of unification variables: *)
and u_type =
  [ `Free of (tyvar * k_var)
  | `Bound of (int * k_var)
  | `Quant of (int * [`All|`Exist] * int * k_var * u_var)
  | `Const of (int * u_typeconst * (u_var * k_var) list * k_var)
  ]
and bound_ty = [ `Rigid | `Flex ]
and 'a bound = {
  b_ty: bound_ty;
  b_at: 'a;
}
and tyvar = {
  ty_id: int;
  ty_flag: bound_ty;
}
and u_var = u_type UnionFind.var

type sign = [ `Pos | `Neg ]

type quantifier = [ `All | `Exist ]

let string_of_typeconst_name = function
  | `Text -> "text"
  | `Int -> "int"
  | `Char -> "char"
  | `Fn -> "->"
  | `Record -> "{...}"
  | `Union -> "|"
  | `Apply -> "<apply>"
  | `Lambda -> "<lambda>"

let sexp_of_typeconst_name n = Sexp.Atom (string_of_typeconst_name n)
