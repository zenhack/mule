let desugar_typecheck expr =
  let open OrErr in
  Lint.check expr
  >> Desugar.desugar expr
  >>= fun dexp ->
    print_endline ("Desugared: " ^ Pretty.expr dexp);
    Typecheck.typecheck dexp
  |>> fun ty ->
    print_endline ("inferred type: " ^ Pretty.typ ty);
    dexp

let rec loop () =
  print_string "#mule> ";
  let line = try read_line () with
    End_of_file ->
      (* Make sure the terminal prompt shows up on a new line: *)
      print_endline "";
      exit 0
  in
  begin match MParser.parse_string Parser.repl_line line () with
  | MParser.Failed (msg, _) ->
      print_endline "Parse Error:";
      print_endline msg
  | MParser.Success None ->
      (* User entered a blank line *)
      ()
  | MParser.Success (Some expr) ->
      begin match desugar_typecheck expr with
      | OrErr.Err e ->
          print_endline (Error.show e)
      | OrErr.Ok dexp ->
          print_endline "Javascript: ";
          (ToJs.toJs dexp |> Ast.Js.Expr.fmt print_string);
          print_endline "";
          Eval.eval dexp
          |> Pretty.expr
          |> fun ret -> print_endline ("Evaluated: " ^ ret)
      end
  end;
  loop ()
