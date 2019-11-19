let config = ref Cli.Debug_flags.{
    print_eval_steps = false;
    always_print_stack_trace = false;
    trace_require_subtype = false;
    debug_steps = false;
    no_js_cps = false;
    no_js_type_requirement = false;
  }

let set new_cfg =
  config := new_cfg

let print_eval_steps () = (!config).print_eval_steps
let always_print_stack_trace () = (!config).always_print_stack_trace
let trace_require_subtype () = (!config).trace_require_subtype
let debug_steps () = (!config).debug_steps
let no_js_cps () = (!config).no_js_cps
let no_js_type_requirement () = (!config).no_js_type_requirement
