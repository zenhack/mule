let interp_cmd = function
  | `Repl ->
      Repl.loop ()
  | `Eval path ->
      Load.load_file (Load.new_loader ()) ~base_path:path ~types:[]
      |> Run.run_load_result
  | `Build_js Cli.{src; dest} ->
      Build_js.build src dest
  | `Run Cli.{runner; file} ->
      begin match Map.find Runners.by_name runner with
        | None ->
            Stdio.eprintf "no such runner\n";
            Caml.exit 1
        | Some runner ->
            let Load.{rt_expr; _} =
              Load.load_file
                (Load.new_loader ())
                ~base_path:file
                ~types:[runner.Runners.want_type]
            in
            Lazy.force rt_expr
            |> runner.Runners.run
            |> Lwt_main.run
            |> ignore
      end

let main () =
  match Cli.parse_cmd () with
  | `Ok result ->
      begin
        Config.set result.debug_flags;
        try
          interp_cmd result.cmd
        with
        | MuleErr.MuleExn err ->
            Report.print_endline (Pretty.error err);
            Caml.exit 1
      end
  | `Version | `Help -> Caml.exit 0
  | `Error _ -> Caml.exit 1
