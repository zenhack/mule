open Common_ast

type typeconst_name =
  [ `Text
  | `Int
  | `Char
  | `Empty
  | `Fn
  | `Record
  | `Union
  | `Apply
  | `Lambda
  | `GetField of [ `Types | `Values ] * Label.t
  | `Fix

  | `Poison
  ]

type typeconst =
  [ `Named of typeconst_name
  | `Extend of Label.t
  ]

type edge_type =
  [ `Structural
  | `Unify
  | `Instance
  | `Sibling
  | `Binding of [ `Flex | `Rigid | `Explicit ]
  ]
type node_type =
  [ `Free
  | `Const of typeconst
  | `Quant
  | `G
  ]
