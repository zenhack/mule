
let slurp_file path =
  let fd = In.create path in
  let str = In.input_all fd in
  In.close fd;
  str

let each_file ~f =
    for i = 2 to Array.length Sys.argv - 1 do
      let path = Array.get Sys.argv i in
      let str = slurp_file path in
      match f str with
      | Ok () -> ()
      | Error () -> Caml.exit 1
    done

let () =
  if Array.length Sys.argv <= 1 then
    Repl.loop ()
  else
    begin match Array.get Sys.argv 1 with
    | "repl" ->
        Repl.loop ()
    | "test" ->
        each_file ~f:Run.run
    | "run" ->
      begin try
        let runner_name = Array.get Sys.argv 2 in
        let file_name = Array.get Sys.argv 3 in
        begin match Map.find Runners.by_name runner_name with
          | None ->
            Out.print_endline "no such runner";
            Caml.exit 1
          | Some runner ->
            let input = slurp_file file_name in
            begin match MParser.parse_string Parser.expr input () with
              | Failed(msg, _) ->
                Out.print_endline ("Parse error: " ^ msg);
                Caml.exit 1
              | Success expr ->
                let result =
                  let expr = Ast.Surface.Expr.WithType(expr, runner.Runners.want_type) in
                  let open Result.Let_syntax in
                  let%bind _ = Lint.check expr in
                  let%bind dexp = Desugar.desugar expr in
                  let%map _ = Typecheck.typecheck dexp in
                  let rt_expr = To_runtime.translate dexp in
                  runner.Runners.run rt_expr
                in
                begin match result with
                  | Ok _ -> ()
                  | Error err ->
                    Out.print_endline (MuleErr.show err);
                    Caml.exit 1
                end
            end
        end
      with Invalid_argument _ ->
        Out.print_endline("not enough arguments to run");
        Caml.exit 1
      end
    | cmd ->
        Out.print_endline ("Invalid command: " ^ cmd);
        Caml.exit 1
    end
