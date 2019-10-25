
type debug_flags = <
  print_eval_steps : bool;
  always_print_stack_trace : bool;
  trace_require_subtype : bool;
  debug_steps : bool;
>

type cmd =
  [ `Repl
  | `Eval of string
  | `Build_js of string
  | `Run of <runner: string; file: string>
  ]

type t = <
  debug_flags : debug_flags;
  cmd : cmd;
>
