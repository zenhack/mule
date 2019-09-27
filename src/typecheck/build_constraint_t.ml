open Types
open Typecheck_types

type built_constraints =
  { unification: unify_edge list
  ; instantiation: (g_node * u_var list) IntMap.t
  ; kind: (reason * k_var * k_var) list
  ; ty: u_var
  }

type constraint_ops =
  { constrain_unify : reason -> u_var -> u_var -> unit
  ; constrain_inst  : g_node -> u_var -> unit
  ; constrain_kind  : reason -> k_var -> k_var -> unit
  }

type context = {
  cops: constraint_ops;
  env_types: u_var VarMap.t;
  env_terms: [ `Ty of u_var | `G of g_node ] Lazy.t VarMap.t;
  g: g_node;
}
