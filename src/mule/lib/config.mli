
val set : Cli.Debug_flags.t -> unit

val print_eval_steps : unit -> bool
val always_print_stack_trace : unit ->  bool
val trace_require_subtype : unit -> bool
val debug_steps : unit -> bool
val no_js_cps : unit -> bool
val no_js_type_requirement : unit -> bool

val browser : unit -> string
