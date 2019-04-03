(* types used by the type checker *)

(* Contents of unification variables for types: *)
type u_type =
  [ `Free of tyvar
  | `Fn of (tyvar * u_type UnionFind.var * u_type UnionFind.var)
  | `Record of (tyvar * u_row UnionFind.var)
  | `Union of (tyvar * u_row UnionFind.var)
  ]
(* ...and rows: *)
and u_row =
  [ `Free of tyvar
  | `Extend of (tyvar * Ast.Label.t * u_type UnionFind.var * u_row UnionFind.var)
  | `Empty of tyvar
  ]
and bound_ty = [ `Rigid | `Flex ]
and 'a bound =
  { b_ty: bound_ty
  ; b_at: 'a
  }
and tyvar =
  { ty_id: int
  ; ty_bound: bound_target bound UnionFind.var
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

type permission = F | R | L

