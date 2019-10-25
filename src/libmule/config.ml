let config = ref (object
    method print_eval_steps = false
    method always_print_stack_trace = false
    method trace_require_subtype = false
    method debug_steps = false
  end)

let set new_cfg =
  config := new_cfg

let print_eval_steps () = (!config)#print_eval_steps
let always_print_stack_trace () = (!config)#always_print_stack_trace
let trace_require_subtype () = (!config)#trace_require_subtype
let debug_steps () = (!config)#debug_steps
