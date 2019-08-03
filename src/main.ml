
let slurp_file (path : string) : string Lwt.t =
  Lwt_io.with_file ~mode:Lwt_io.Input path Lwt_io.read

let each_file : f:(string -> 'a Lwt.t) -> unit Lwt.t =
  fun ~f ->
  let rec go i =
    if i < Array.length Sys.argv then
      begin
        let path = Array.get Sys.argv i in
        let%lwt contents = slurp_file path in
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

let main () =
  if Array.length Sys.argv <= 1 then
    Repl.loop ()
  else
    begin match Array.get Sys.argv 1 with
      | "repl" ->
          Repl.loop ()
      | "test" ->
          each_file ~f:(fun input ->
              let%lwt _ = Run.run input in
              Lwt.return ()
            )
      | "run" ->
          begin try%lwt
              let runner_name = Array.get Sys.argv 2 in
              let file_name = Array.get Sys.argv 3 in
              begin match Map.find Runners.by_name runner_name with
                | None ->
                    let%lwt _ = Lwt_io.write Lwt_io.stderr "no such runner\n" in
                    Caml.exit 1
                | Some runner ->
                    let%lwt input = slurp_file file_name in
                    begin match MParser.parse_string Parser.expr input () with
                      | Failed(msg, _) ->
                          let%lwt _ = Lwt_io.write Lwt_io.stderr ("Parse error: " ^ msg ^ "\n") in
                          Caml.exit 1
                      | Success expr ->
                          begin try%lwt
                              let expr = Ast.Surface.Expr.WithType(expr, runner.Runners.want_type) in
                              let _ = Lint.check expr in
                              let dexp = Desugar.desugar expr in
                              let _ = Typecheck.typecheck dexp in
                              let rt_expr = To_runtime.translate dexp in
                              let%lwt _ = runner.Runners.run rt_expr in
                              Lwt.return ()
                            with
                            | MuleErr.MuleExn err ->
                                let%lwt _ = Lwt_io.write Lwt_io.stderr (MuleErr.show err ^ "\n") in
                                Caml.exit 1
                          end
                    end
              end
            with
            | Invalid_argument _ ->
                let%lwt _ = Lwt_io.write Lwt_io.stderr "not enough arguments to run\n" in
                Caml.exit 1
            | e ->
                raise e
          end
      | cmd ->
          let%lwt _ = Lwt_io.write Lwt_io.stderr ("Invalid command: " ^ cmd ^ "\n") in
          Caml.exit 1
    end

let () =
  Lwt_main.run (main ())
