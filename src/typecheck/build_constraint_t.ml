open Typecheck_types

type built_constraints =
  { unification: unify_edge list
  ; instantiation: (g_node * (u_type UnionFind.var) list) IntMap.t
  ; kind: (k_var * k_var) list
  ; ty: u_type UnionFind.var
  }

type constraint_ops =
  { constrain_unify : u_type UnionFind.var -> u_type UnionFind.var -> unit
  ; constrain_inst  : g_node -> u_type UnionFind.var -> unit
  ; constrain_kind  : k_var -> k_var -> unit
  }
