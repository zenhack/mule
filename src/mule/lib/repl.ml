
let must_read_line () =
  try
    Caml.read_line ()
  with
    | End_of_file ->
        (* Make sure the terminal prompt shows up on a new line: *)
        Stdio.print_endline "";
        Caml.exit 0
    | e ->
        raise e

let run_line : Load.loader -> string -> unit =
  fun loader line ->
    match MParser.parse_string Parser.repl_line line "./<repl>" with
    | MParser.Failed (msg, _) ->
        Report.display_always "Parse Error" msg
    | MParser.Success None ->
        (* empty input *)
        ()
    | MParser.Success (Some expr) ->
        Run.run_load_result
          (Load.load_surface_ast loader ~typ:None ~expr ~extra_types:[])

let rec loop : unit -> 'a = fun () ->
  let loader = Load.new_loader () in
  Report.print_string "#mule> ";
  run_line loader (must_read_line ());
  loop ()
