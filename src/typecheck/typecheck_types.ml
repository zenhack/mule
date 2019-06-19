(* types used by the type checker *)

type u_kind =
  [ `Row
  | `Type
  ]

type u_typeconst =
  [ `Named of string
  | `Extend of Ast.Label.t
  ]
(* Contents of unification variables: *)
and u_type =
  [ `Free of (tyvar * u_kind)
  | `Quant of (tyvar * u_type UnionFind.var)
  | `Const of (tyvar * u_typeconst * (u_type UnionFind.var * u_kind) list * u_kind)
  ]
and bound_ty = [ `Rigid | `Flex | `Explicit ]
and 'a bound =
  { b_ty: bound_ty
  ; b_at: 'a
  }
and tyvar =
  { ty_id: int
  ; ty_bound: bound_target bound ref
  }
and g_node =
  { g_id: int
  ; g_bound: (g_node bound) option
  ; g_child: u_type UnionFind.var Lazy.t
  }
and bound_target =
  [ `Ty of u_type UnionFind.var Lazy.t
  | `G of g_node
  ]

type u_var = u_type UnionFind.var

type sign = [ `Pos | `Neg ]

type quantifier = [ `All | `Exist ]

let flip_sign = function
  | `Pos -> `Neg
  | `Neg -> `Pos

let get_flag: quantifier -> sign -> bound_ty =
  fun q sign-> match q, sign with
    | `All, `Pos -> `Flex
    | `All, `Neg -> `Rigid
    | `Exist, `Pos -> `Rigid
    | `Exist, `Neg -> `Flex

(* constructors for common type constants. *)
let int tv = `Const(tv, `Named "int", [], `Type)
let fn tv param ret = `Const(tv, `Named "->", [param, `Type; ret, `Type], `Type)
let union tv row = `Const(tv, `Named "|", [row, `Row], `Type)
let record tv r_types r_values = `Const(tv, `Named "{...}", [r_types, `Row; r_values, `Row], `Type)
let empty tv = `Const(tv, `Named "<empty>", [], `Row)
let extend tv lbl head tail = `Const(tv, `Extend lbl, [head, `Type; tail, `Row], `Row)

type permission = F | R | L | E

type unify_edge =
  | Unify of (u_type UnionFind.var * u_type UnionFind.var)

type inst_edge =
  { ie_g_node: g_node
  ; ie_ty_node: u_type UnionFind.var
  }

let typeconst_eq: u_typeconst -> u_typeconst -> bool = Poly.equal
let perm_eq: permission -> permission -> bool = Poly.equal

let get_tyvar: u_type -> tyvar = function
  | `Free (v, _) -> v
  | `Const (v, _, _, _) -> v
  | `Quant (v, _) -> v
let get_u_bound x = !((get_tyvar x).ty_bound)
