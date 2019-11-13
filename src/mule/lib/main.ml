open Common_ast

let load_and_typecheck typ file_name =
  let input = Stdio.In_channel.read_all file_name in
  let full_path = Caml.Filename.current_dir_name ^ "/" ^ file_name in
  match MParser.parse_string Parser.expr_file input full_path with
  | Failed(msg, _) ->
      Stdio.eprintf "Parse error : %s\n" msg;
      Caml.exit 1
  | Success expr ->
      begin try
          let _ = Lint.check expr in
          let dexp = Desugared_ast_expr.WithType {
              wt_expr = Desugar.desugar expr;
              wt_type = typ;
            }
          in
          let _ = Typecheck.typecheck dexp in
          dexp
        with
        | MuleErr.MuleExn err ->
            Stdio.eprintf "%s\n" (MuleErr.show err);
            Caml.exit 1
      end

let exec_lwt lwt = ignore (Lwt_main.run lwt)

let interp_cmd = function
  | `Repl ->
      exec_lwt (Repl.loop ())
  | `Eval path ->
      let contents = Stdio.In_channel.read_all path in
      exec_lwt (Run.run contents)
  | `Build_js flags ->
      let src = flags#src in
      let dest = match flags#dest with
        | Some d -> d
        | None -> src ^ ".js"
      in
      begin try
          let v = Var.of_string "t" in
          let dexp =
            load_and_typecheck
              Desugared_ast_type.(
                (* For now we're not imposing any particular type,
                 * so we just set it as `exists t. t`. *)
                Quant {
                  q_info = `Type;
                  q_quant = `Exist;
                  q_var = v;
                  q_body = Var {
                      v_info = `Unknown;
                      v_var = v;
                      v_src = `Generated;
                    };
                }
              )
              src
          in
          let text =
            To_js.translate_expr dexp
            |> (fun e ->
              if Config.no_js_cps () then
                e
              else
                Js_pre.cps (fun x -> x) e
            )
            |> Js_pre.to_js
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
        with
        | Invalid_argument _ ->
            Stdio.eprintf "not enough arguments to build-js\n";
            Caml.exit 1
        | e ->
            raise e
      end
  | `Run targ ->
      let runner_name = targ#runner in
      let file_name = targ#file in
      begin match Map.find Runners.by_name runner_name with
        | None ->
            Stdio.eprintf "no such runner\n";
            Caml.exit 1
        | Some runner ->
            let dexp = load_and_typecheck runner.Runners.want_type file_name in
            let rt_expr = To_runtime.translate dexp in
            exec_lwt (runner.Runners.run rt_expr)
      end

let main () =
  match Cli.parse_cmd () with
  | `Ok result ->
      Config.set result#debug_flags;
      interp_cmd result#cmd
  | `Version | `Help -> Caml.exit 0
  | `Error _ -> Caml.exit 1
