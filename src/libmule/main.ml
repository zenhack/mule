open Common_ast

let load_and_typecheck typ file_name =
  let%lwt input = Util.IO.slurp_file file_name in
  let full_path = Caml.Filename.current_dir_name ^ "/" ^ file_name in
  match MParser.parse_string Parser.expr_file input full_path with
  | Failed(msg, _) ->
      let%lwt _ = Lwt_io.write Lwt_io.stderr ("Parse error: " ^ msg ^ "\n") in
      Caml.exit 1
  | Success expr ->
      begin try%lwt
          let _ = Lint.check expr in
          let dexp = Desugared_ast_expr.WithType {
              wt_expr = Desugar.desugar expr;
              wt_type = typ;
            }
          in
          let _ = Typecheck.typecheck dexp in
          Lwt.return dexp
        with
        | MuleErr.MuleExn err ->
            let%lwt _ = Lwt_io.write Lwt_io.stderr (MuleErr.show err ^ "\n") in
            Caml.exit 1
      end

let interp_cmd = function
  | `Repl -> Repl.loop ()
  | `Eval path ->
      let%lwt contents = Util.IO.slurp_file path in
      let%lwt _ = Run.run contents in
      Lwt.return ()
  | `Build_js flags ->
      let src = flags#src in
      let dest = match flags#dest with
        | Some d -> d
        | None -> src ^ ".js"
      in
      begin try%lwt
          let v = Var.of_string "t" in
          let%lwt dexp =
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
                    };
                }
              )
              src
          in
          Lwt_io.with_file dest ~mode:Lwt_io.output (fun out ->
            To_js.translate_expr dexp
            |> Js_pre.cps (fun x -> x)
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
            |> Lwt_io.write out
          )
        with
        | Invalid_argument _ ->
            let%lwt _ = Lwt_io.write Lwt_io.stderr "not enough arguments to build-js\n" in
            Caml.exit 1
        | e ->
            raise e
      end
  | `Run targ ->
      let runner_name = targ#runner in
      let file_name = targ#file in
      begin match Map.find Runners.by_name runner_name with
        | None ->
            let%lwt _ = Lwt_io.write Lwt_io.stderr "no such runner\n" in
            Caml.exit 1
        | Some runner ->
            let%lwt dexp = load_and_typecheck runner.Runners.want_type file_name in
            let rt_expr = To_runtime.translate dexp in
            let%lwt _ = runner.Runners.run rt_expr in
            Lwt.return ()
      end

let main () =
  match Cli.parse_cmd () with
  | `Ok result ->
      Config.set result#debug_flags;
      interp_cmd result#cmd
  | `Version | `Help -> Caml.exit 0
  | `Error _ -> Caml.exit 1

let main () =
  Lwt_main.run (main ())
