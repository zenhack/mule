module Debug_flags = struct
  type t = {
    print_eval_steps : bool;
    always_print_stack_trace : bool;
    trace_require_subtype : bool;
    debug_steps : bool;
    no_js_cps : bool;
    no_js_type_requirement : bool;
  }
end

type build_js_cmd = {
  src: string;
  dest: string option;
}

type run_cmd = {
  runner: string;
  file: string;
}

type cmd =
  [ `Repl
  | `Eval of string
  | `Build_js of build_js_cmd
  | `Run of run_cmd
  ]

type t = {
  debug_flags : Debug_flags.t;
  cmd : cmd;
}
