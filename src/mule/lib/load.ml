
type result = {
  typ: int Desugared_ast_type_t.t;
  rt_expr: Runtime_ast.Expr.t Lazy.t;
  js_expr: Js_ast_t.expr Lazy.t;
}

let load_surface_ast ~typ ~expr =
  let expr = match typ with
    | None -> expr
    | Some t -> Common_ast.Loc.{
        l_value = Surface_ast.Expr.WithType {
          wt_type = t;
          wt_term = expr;
        };
        l_loc = expr.l_loc;
      }
  in
  Lint.check expr;
  let dexp = Desugar.desugar expr in
  Report.display "Desugared" (Pretty.expr dexp);
  let typ = Typecheck.typecheck dexp in
  Report.display "inferred type"  (Pretty.typ typ);
  let rt_expr = lazy (To_runtime.translate dexp) in
  let js_expr =
    lazy (
      let e = To_js.translate_expr dexp in
      let e =
        if Config.no_js_cps () then
          e
        else
          Js_pre.cps (fun x -> x) e
      in
      Js_pre.to_js e
    )
  in
  {typ; rt_expr; js_expr}

let maybe_chop_suffix str suffix =
  let suffix_len = String.length suffix in
  if String.equal (String.suffix str suffix_len) suffix then
    String.prefix str (String.length str - suffix_len)
  else
    str

let load_file ~base_path =
  let parse_all parser_ path =
    let full_path = Caml.Sys.getcwd () ^ "/" ^ path in
    let src = Stdio.In_channel.read_all path in
    match MParser.parse_string parser_ src full_path with
    | Failed(msg, _) ->
        Stdio.eprintf "Parse error : %s\n" msg;
        Caml.exit 1
    | Success value ->
        value
  in
  let base_path = maybe_chop_suffix base_path ".mule" in
  let expr = parse_all Parser.expr_file (base_path ^ ".mule") in
  let typ =
    (* It would be slightly more correct to just call parse_all
     * and then catch the appropriate exception, since otherwise
     * there's a race condition here, but:
     *
     * - read_all throws a generic Sys_error exception, with a string
     *   message, so it's not easy to distinguish the file not existing
     *   from other errors.
     * - concurrent modifications to the source code we're loading isn't
     *   something we're interested in dealing with anyway.
     *)
    let type_path = base_path ^ ".msig" in
    if Caml.Sys.file_exists type_path then
      Some (parse_all Parser.type_file type_path)
    else
      None
  in
  load_surface_ast ~typ ~expr
