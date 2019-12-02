
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
and u_quant = {
  q_id : int;
  q_quant : [ `All | `Exist ];
  q_var : u_bound_var;
  q_kind: k_var;
  q_body: u_var;
}
and u_bound_var = {
  bv_id: int;
  bv_info: var_info;
  bv_kind: k_var;
}
and u_type =
  [ `Free of (tyvar * k_var)
  | `Bound of u_bound_var
  | `Quant of u_quant
  | `Const of (int * u_typeconst * (u_var * k_var) list * k_var)
  ]
and bound_ty = [ `Rigid | `Flex ]
and tyvar = {
  ty_id: int;
  ty_flag: bound_ty;
  ty_scope: Scope.t;
  ty_info: var_info;
}
and var_info = {
  vi_name: string option;
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
