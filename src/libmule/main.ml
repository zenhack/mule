open Common_ast

let each_file : f:(string -> 'a Lwt.t) -> unit Lwt.t =
  fun ~f ->
  let rec go i =
    if i < Array.length Sys.argv then
      begin
        let path = Array.get Sys.argv i in
        let%lwt contents = Util.IO.slurp_file path in
        let%lwt () = f contents in
        go (i + 1)
      end
    else
      Lwt.return ()
  in
  go 2

let exit_msg msg =
  let%lwt _ = Lwt_io.write Lwt_io.stderr ("Parse error: " ^ msg ^ "\n") in
  Caml.exit 1

let load_and_typecheck typ file_name =
  let%lwt input = Util.IO.slurp_file file_name in
  let full_path = Caml.Filename.current_dir_name ^ "/" ^ file_name in
  match MParser.parse_string Parser.expr_file input full_path with
  | Failed(msg, _) ->
      let%lwt _ = Lwt_io.write Lwt_io.stderr ("Parse error: " ^ msg ^ "\n") in
      Caml.exit 1
  | Success expr ->
      begin try%lwt
          let expr = Surface_ast.Expr.WithType {
              wt_term = expr;
              wt_type = typ;
            }
          in
          let _ = Lint.check expr in
          let dexp = Desugar.desugar expr in
          let _ = Typecheck.typecheck dexp in
          Lwt.return dexp
        with
        | MuleErr.MuleExn err ->
            let%lwt _ = Lwt_io.write Lwt_io.stderr (MuleErr.show err ^ "\n") in
            Caml.exit 1
      end

let interp_cmd = function
  | `Repl -> Repl.loop ()
  | `Test path ->
      let%lwt contents = Util.IO.slurp_file path in
      let%lwt _ = Run.run contents in
      Lwt.return ()
  | `Build_js file_name ->
        begin try%lwt
          let%lwt dexp =
            load_and_typecheck
              Surface_ast.Type.(
                (* For now we're not imposing any particular type,
                 * so we just set it as `exists t. t`.
                *)
                let v = Var.of_string "t" in
                Quant {
                  q_quant = `Exist;
                  q_vars = [v];
                  q_body = Var {v_var = v};
                }
              )
              file_name
          in
          let out = Lwt_io.stdout in
          let%lwt _ = Lwt_io.write out Js_runtime.src in
          To_js.translate_expr dexp
          |> Js_pre.cps (fun x -> x)
          |> Js_pre.to_js
          |> Js_ast.expr
          |> Fmt.(fun x -> x ^ s "\n")
          |> Fmt.to_string
          |> Lwt_io.write out
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
  | `Ok cmd -> interp_cmd cmd
  | `Version | `Help -> Caml.exit 0
  | `Error _ -> Caml.exit 1

let main () =
  Lwt_main.run (main ())