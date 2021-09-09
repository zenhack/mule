let run_load_result: Load.result -> unit =
  fun Load.{typ; rt_expr; _} ->
  let rt_expr = Lazy.force rt_expr in
  Report.display "Runtime term" (fun () -> Pretty.runtime_expr rt_expr);
  let ret = Eval.eval rt_expr in
  Report.display "Evaluated" (fun () -> Pretty.runtime_expr ret);
  if not (Config.debug_steps ()) then
    begin
      Report.print_endline (String.concat [
          "it : ";
          Desugared_ast_type.to_string
          (* XXX/TODO: I am at a complete loss as to why the map is necessary
             here; the type annotation on [to_string] clearly indicates its
             argument is polymorphic, but without this I get a complaint
             that it's expecting [unit t] instead of [int t]. It should take
             either. WTF? Should debug this at some point, but fortunatley
             for our purposes here it works to just convert it. *)
            (Desugared_ast_type.map ~f:(fun _ -> ()) typ);
          " =";
        ]);
      Report.print_endline ("  " ^ Runtime_ast.Expr.to_string ret)
    end
