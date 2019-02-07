let rec loop () =
  print_string "#ready> ";
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
      begin match Typecheck.typecheck expr with
      | OrErr.Err (Error.UnboundVar (Ast.Var name)) ->
          print_endline ("unbound variable: " ^ name);
      | OrErr.Err Error.TypeMismatch ->
          (* Most useful error message EVER: *)
          print_endline "Type mismatch"
      | OrErr.Ok ty ->
          print_endline ("inferred type: " ^ Pretty.typ ty);
          Desugar.desugar expr
            |> Eval.eval
            |> Ast.Desugared.Pretty.expr
            |> print_endline;
      end
  end;
  loop ()

let () = loop ()
