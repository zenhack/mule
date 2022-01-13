
type expr =
  | Var of string
  | Call of (expr * expr list)
  | Index of (expr * expr)
  | Array of expr list
  | Object of fields
  | String of string
  | BigInt of Z.t
  | Int of int
  | Lam of
      ( string list
        * [ `E of expr (* Single expression *)
          | `S of block (* Statements *)
        ]
      )
  | Null
  (* {...foo, x: 1, y :2 } // TODO what does js actually call this? *)
  | RecordUpdate of (expr * fields)
and fields = (string * expr) list
and stmt =
  | Return of expr
  | Switch of {
      sw_scrutinee: expr;
      sw_cases: (expr * block) list;
      sw_default: block option;
    }
  | VarDecl of (string * expr)
and block =
  stmt list
