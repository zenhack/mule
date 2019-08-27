open Common_ast

type reason =
  [ `AppParamArg
  | `Lambda
  | `KnownKind of [ `Fn | `Recur | `Quant | `Row ]
  | `ExtendTail of (reason * [`L | `R])
  | `MatchSiblingsBody
  | `MatchSiblingsPattern
  | `MatchDefault
  | `VarUse of <
      bind_type : [ `Lambda | `Let | `LetType ];
      var : Var.t
    >
  | `TypePath of <
      bind_type : [ `Lambda | `Let ];
      var : Var.t;
      lbls : Label.t list;
    >
  | `Frontier
  | `Propagate
  | `Cascade of (reason * int)
  ]
