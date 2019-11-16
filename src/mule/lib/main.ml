let load_and_typecheck typ file_name =
  let input = Stdio.In_channel.read_all file_name in
  let full_path = Caml.Filename.current_dir_name ^ "/" ^ file_name in
  match MParser.parse_string Parser.expr_file input full_path with
  | Failed(msg, _) ->
      Stdio.eprintf "Parse error : %s\n" msg;
      Caml.exit 1
  | Success expr ->
      let _ = Lint.check_expr expr in
      let dexp = Desugared_ast_expr.WithType {
          wt_expr = Desugar.desugar expr;
          wt_type = typ;
        }
      in
      let _ = Typecheck.typecheck dexp in
      dexp

let interp_cmd = function
  | `Repl ->
      Repl.loop ()
  | `Eval path ->
      let contents = Stdio.In_channel.read_all path in
      Run.run contents
  | `Build_js Cli.{src; dest}->
      let dest = match dest with
        | Some d -> d
        | None -> src ^ ".js"
      in
      let Load.{js_expr; _} = Load.load_file ~base_path:src ~types:[] in
      let text =
        Lazy.force js_expr
        |> Js_ast.expr
        |> Fmt.(fun e -> concat [
            s "const mule = (() => {";
            s Js_runtime_gen.src; s "\n";
            s "mule.main = "; e; s "\n";
            s "return mule\n";
            s "})()\n";
          ])
        |> Fmt.to_string
      in
      Stdio.Out_channel.write_all dest ~data:text
  | `Run Cli.{runner; file} ->
      begin match Map.find Runners.by_name runner with
        | None ->
            Stdio.eprintf "no such runner\n";
            Caml.exit 1
        | Some runner ->
            let Load.{rt_expr; _} =
              Load.load_file ~base_path:file ~types:[runner.Runners.want_type]
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
