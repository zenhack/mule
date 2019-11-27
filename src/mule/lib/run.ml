let run_load_result: Load.result -> unit =
  fun Load.{typ; rt_expr; _} ->
  let rt_expr = Lazy.force rt_expr in
  Report.display "Runtime term" (fun () -> Pretty.runtime_expr rt_expr);
  let ret = Eval.eval rt_expr in
  Report.display "Evaluated" (fun () -> Pretty.runtime_expr ret);
  if not (Config.debug_steps ()) then
    Report.print_endline ("it : " ^ Desugared_ast_type.to_string typ ^ " =");
    Report.print_endline ("  " ^ Runtime_ast.Expr.to_string ret)
