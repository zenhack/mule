open OrErr

let desugar_typecheck expr =
  Lint.check expr
  >> Desugar.desugar expr
  >>= fun dexp ->
    print_endline ("Desugared: " ^ Pretty.expr dexp);
    Typecheck.typecheck dexp
  |>> fun ty ->
    print_endline ("inferred type: " ^ Pretty.typ ty);
    dexp

let run input =
  (* We really ought to rename repl line, since it's actually what we want
   * regardless of whether we're at the repl: *)
  match MParser.parse_string Parser.repl_line input () with
  | MParser.Failed (msg, _) ->
      print_endline "Parse Error:";
      print_endline msg;
      Err ()
  | MParser.Success None ->
      (* empty input *)
      Ok ()
  | MParser.Success (Some expr) ->
      begin match desugar_typecheck expr with
      | Err e ->
          print_endline (Error.show e);
          Err ()
      | Ok dexp ->
          print_endline "Javascript: ";
          (ToJs.toJs dexp |> Ast.Js.Expr.fmt print_string);
          print_endline "";
          Eval.eval dexp
          |> Pretty.expr
          |> fun ret -> print_endline ("Evaluated: " ^ ret);
          Ok ()
      end
