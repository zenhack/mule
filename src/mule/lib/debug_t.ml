open Typecheck_types_t

type edge_type =
  [ `Structural
  | `Unify
  | `Instance
  | `Sibling
  | `Binding of [ `Flex | `Rigid | `Explicit ]
  ]
type node_type =
  [ `Free of [ `Flex | `Rigid ]
  | `Bound
  | `Const of u_typeconst
  | `Quant
  | `G
  ]
