
let print_endline s =
  Stdio.print_endline s;
  Stdio.Out_channel.flush Stdio.stdout

let display_always label text =
  let text =
    String.split_lines text
    |> List.map ~f:(fun line -> "\t" ^ line)
    |> String.concat ~sep:"\n"
  in
  print_endline ("\n" ^ label ^ ":\n\n" ^ text)

let display label text =
  if Config.debug_steps () then
    display_always label text

let desugar_typecheck expr =
  let _ = Lint.check expr in
  let dexp = Desugar.desugar expr in
  let _ = display "Desugared" (Pretty.expr dexp) in
  let ty = Typecheck.typecheck dexp in
  let _ = display "inferred type"  (Pretty.typ ty) in
  (ty, dexp)

let run : string -> unit = fun input ->
  (* We really ought to rename repl line, since it's actually what we want
   * regardless of whether we're at the repl: *)
  let path = Caml.Filename.current_dir_name ^ "/<repl>" in
  match MParser.parse_string Parser.repl_line input path with
  | MParser.Failed (msg, _) ->
      display_always "Parse Error" msg
  | MParser.Success None ->
      (* empty input *)
      ()
  | MParser.Success (Some expr) ->
      try
        begin
          let (ty, dexp) = desugar_typecheck expr in
          let rexp = To_runtime.translate dexp in
          display "Runtime term" (Pretty.runtime_expr rexp);
          let ret = Eval.eval rexp in
          display "Evaluated" (Pretty.runtime_expr ret);
          if not (Config.debug_steps ()) then
            print_endline
              (Runtime_ast.Expr.to_string ret
               ^ " : "
               ^ Desugared_ast_type.to_string ty
              )
        end
      with
      | MuleErr.MuleExn e ->
          print_endline (Pretty.error e)
