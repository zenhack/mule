open Typecheck_types

type edge_type =
  [ `Structural
  | `Unify
  | `Instance
  | `Sibling
  | `Binding of [ `Flex | `Rigid | `Explicit ]
  ]
type node_type =
  [ `TyVar
  | `Const of u_typeconst
  | `G
  ]
