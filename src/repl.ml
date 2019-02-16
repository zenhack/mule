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
      | OrErr.Err (Error.UnboundVar var) ->
          print_endline ("unbound variable: " ^ Ast.Var.to_string var);
      | OrErr.Err Error.TypeMismatch ->
          (* Most useful error message EVER: *)
          print_endline "Type mismatch"
      | OrErr.Err Error.UnreachableCases ->
          print_endline "Unreachable cases in match"
      | OrErr.Err (Error.DuplicateFields fields) ->
          print_endline "Duplicate fields:";
          fields
            |> List.map Ast.Label.to_string
            |> String.concat ","
            |> print_endline
      | OrErr.Err Error.EmptyMatch ->
          print_endline "Empty match expression."
      | OrErr.Ok dexp ->
          Eval.eval dexp
          |> Pretty.expr
          |> fun ret -> print_endline ("Evaluated: " ^ ret)
      end
  end;
  loop ()
