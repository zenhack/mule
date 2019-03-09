

let dump_constraints: bool =
  Sys.getenv_opt "DUMP_CONSTRAINTS" = Some "1"

let render_constraints: bool =
  Sys.getenv_opt "RENDER_CONSTRAINTS" = Some "1"
