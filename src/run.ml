open Result.Monad_infix

let desugar_typecheck expr =
  Lint.check expr
  >>= fun _ -> Desugar.desugar expr
  >>= fun dexp ->
    Stdio.print_endline ("Desugared: " ^ Pretty.expr dexp);
    Typecheck.typecheck dexp
  >>| fun ty ->
    Stdio.print_endline ("inferred type: " ^ Pretty.typ ty);
    dexp

let run input =
  (* We really ought to rename repl line, since it's actually what we want
   * regardless of whether we're at the repl: *)
  match MParser.parse_string Parser.repl_line input () with
  | MParser.Failed (msg, _) ->
      Stdio.print_endline "Parse Error:";
      Stdio.print_endline msg;
      Error ()
  | MParser.Success None ->
      (* empty input *)
      Ok ()
  | MParser.Success (Some expr) ->
      begin match desugar_typecheck expr with
      | Error e ->
          Stdio.print_endline (MuleErr.show e);
          Error ()
      | Ok dexp ->
          let rexp = To_runtime.translate dexp in
          Stdio.print_endline ("Runtime term: " ^ Pretty.runtime_expr rexp);
          let ret = Eval.eval rexp in
          Stdio.print_endline ("Evaluated: " ^ Pretty.runtime_expr ret);
          Ok ()
      end
