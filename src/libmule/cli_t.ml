
type t =
  [ `Repl
  | `Eval of string
  | `Build_js of string
  | `Run of <runner: string; file: string>
  ]
