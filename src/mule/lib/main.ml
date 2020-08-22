
let typecheck path =
  let src = Stdio.In_channel.read_all path in
  let exp =
    match MParser.parse_string Parser.expr_file src path with
    | Failed(msg, _) ->
        Stdio.eprintf "Parse error : %s\n" msg;
        Caml.exit 1
    | Success value ->
        value
  in
  Lint.check_expr exp;
  let dexp = Desugar.desugar exp in
  let _ = dexp in
  failwith "TODO"


let interp_cmd = function
  | `Repl ->
      Repl.loop ()
  | `Eval path ->
      Load.load_file
        (Load.new_loader ())
        ~base_path:path
        ~types:[]
        ~export:false
      |> Run.run_load_result
  | `TypeCheck path ->
      typecheck path
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
                ~export:true (* Arbitrary, since we don't use the type. *)
                ~types:[(`Main, runner.Runners.want_type)]
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
