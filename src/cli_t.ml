
type t =
  [ `Repl
  | `Test of string
  | `Build_js of string
  | `Run of <runner: string; file: string>
  ]
