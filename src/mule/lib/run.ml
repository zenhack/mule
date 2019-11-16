let run_load_result: Load.result -> unit =
  fun Load.{typ; rt_expr; _} ->
    let rt_expr = Lazy.force rt_expr in
    Report.display "Runtime term" (Pretty.runtime_expr rt_expr);
    let ret = Eval.eval rt_expr in
    Report.display "Evaluated" (Pretty.runtime_expr ret);
    if not (Config.debug_steps ()) then
      Report.print_endline
        (Runtime_ast.Expr.to_string ret
         ^ " : "
         ^ Desugared_ast_type.to_string typ
        )

let run : string -> unit = fun input ->
  let path = Caml.Filename.current_dir_name ^ "/<repl>" in
  match MParser.parse_string Parser.repl_line input path with
  | MParser.Failed (msg, _) ->
      Report.display_always "Parse Error" msg
  | MParser.Success None ->
      (* empty input *)
      ()
  | MParser.Success (Some expr) ->
      run_load_result (Load.load_surface_ast ~typ:None ~expr)
