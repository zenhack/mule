let env_equal =
  Option.equal String.equal

let flag: string -> bool =
  fun name -> env_equal (Caml.Sys.getenv_opt name) (Some "1")

let dump_constraints   = flag "DUMP_CONSTRAINTS"
let render_constraints = flag "RENDER_CONSTRAINTS"
let print_eval_steps   = flag "PRINT_EVAL_STEPS"
