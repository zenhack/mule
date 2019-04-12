open Result.Monad_infix

let display label text =
  Stdio.print_endline ("\n" ^ label ^ ":\n\n\t" ^ text)

let desugar_typecheck expr =
  Lint.check expr
  >>= fun _ -> Desugar.desugar expr
  >>= fun dexp ->
    display "Desugared" (Pretty.expr dexp);
    Typecheck.typecheck dexp
  >>| fun ty ->
    display "inferred type"  (Pretty.typ ty);
    dexp

let run input =
  (* We really ought to rename repl line, since it's actually what we want
   * regardless of whether we're at the repl: *)
  match MParser.parse_string Parser.repl_line input () with
  | MParser.Failed (msg, _) ->
      display "Parse Error" msg;
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
          display "Runtime term" (Pretty.runtime_expr rexp);
          let ret = Eval.eval rexp in
          display "Evaluated" (Pretty.runtime_expr ret);
          Ok ()
      end
