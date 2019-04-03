open Typecheck_types

type built_constraints =
  { unification: unify_edge list
  ; instantiation: (g_node * (u_type UnionFind.var) list) IntMap.t
  ; ty: u_type UnionFind.var
  }

type constraint_ops =
  { constrain_ty   : u_type UnionFind.var -> u_type UnionFind.var -> unit
  ; constrain_row  : u_row UnionFind.var  -> u_row UnionFind.var  -> unit
  ; constrain_inst : g_node -> u_type UnionFind.var -> unit
  }
