
let desugar_typecheck expr =
  let _ = Lint.check expr in
  let dexp = Desugar.desugar expr in
  let _ = Report.display "Desugared" (Pretty.expr dexp) in
  let ty = Typecheck.typecheck dexp in
  let _ = Report.display "inferred type"  (Pretty.typ ty) in
  (ty, dexp)

let run : string -> unit = fun input ->
  (* We really ought to rename repl line, since it's actually what we want
   * regardless of whether we're at the repl: *)
  let path = Caml.Filename.current_dir_name ^ "/<repl>" in
  match MParser.parse_string Parser.repl_line input path with
  | MParser.Failed (msg, _) ->
      Report.display_always "Parse Error" msg
  | MParser.Success None ->
      (* empty input *)
      ()
  | MParser.Success (Some expr) ->
      try
        begin
          let (ty, dexp) = desugar_typecheck expr in
          let rexp = To_runtime.translate dexp in
          Report.display "Runtime term" (Pretty.runtime_expr rexp);
          let ret = Eval.eval rexp in
          Report.display "Evaluated" (Pretty.runtime_expr ret);
          if not (Config.debug_steps ()) then
            Report.print_endline
              (Runtime_ast.Expr.to_string ret
               ^ " : "
               ^ Desugared_ast_type.to_string ty
              )
        end
      with
      | MuleErr.MuleExn e ->
          Report.print_endline (Pretty.error e)
