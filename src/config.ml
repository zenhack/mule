open Base

let env_equal =
  Option.equal String.equal

let dump_constraints: bool =
  env_equal (Caml.Sys.getenv_opt "DUMP_CONSTRAINTS") (Some "1")

let render_constraints: bool =
  env_equal (Caml.Sys.getenv_opt "RENDER_CONSTRAINTS") (Some "1")
