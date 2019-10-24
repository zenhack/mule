let env_equal =
  Option.equal String.equal

let flag: string -> bool =
  fun name -> env_equal (Caml.Sys.getenv_opt name) (Some "1")

let render_constraints = flag "RENDER_CONSTRAINTS"
let print_eval_steps   = flag "PRINT_EVAL_STEPS"
let always_print_stack_trace = flag "ALWAYS_PRINT_STACK_TRACE"
let trace_require_subtype = flag "TRACE_REQUIRE_SUBTYPE"
let debug_steps = flag "DEBUG_STEPS"

let browser: string =
  match Caml.Sys.getenv_opt "BROWSER" with
  | Some b -> b
  | None -> "firefox"
