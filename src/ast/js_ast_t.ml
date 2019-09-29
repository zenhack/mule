
type expr =
  | Var of string
  | Call of (expr * expr list)
  | Index of (expr * expr)
  | Array of expr list
  | Object of (string * expr) list
  | String of string
  | LamE of (string list * expr) (* Single-expression lambda *)
  | LamS of (string list * block) (* Lambda with statements in the body. *)
and stmt =
  | Return of expr
  | Switch of {
      sw_scrutinee: expr;
      sw_cases: (expr * block) list;
      sw_default: block option;
    }
and block =
  stmt list
