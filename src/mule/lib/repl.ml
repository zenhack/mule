
let history_filename = ".mule_history"

let setup_linenoise () =
  LNoise.history_load ~filename:history_filename |> ignore;
  LNoise.history_set ~max_length:100 |> ignore

let must_read_line () =
  match LNoise.linenoise "#mule> " with
  | None ->
      (* Make sure the terminal prompt shows up on a new line: *)
      Stdio.print_endline "";
      Caml.exit 0
  | Some v ->
      LNoise.history_add v |> ignore;
      LNoise.history_save ~filename:history_filename |> ignore;
      v

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
        (Load.load_surface_ast
            loader
            ~expr
            ~extra_types:[]
            ~export:false
        )

let rec loop : unit -> 'a = fun () ->
  let loader = Load.new_loader () in
  setup_linenoise ();
  begin
    try
      run_line loader (must_read_line ())
    with
    | MuleErr.MuleExn e ->
        Report.print_endline (Pretty.error e)
  end;
  loop ()
