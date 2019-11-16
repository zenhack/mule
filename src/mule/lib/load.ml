include Load_t

type loader = unit

let new_loader () = ()

let load_surface_ast () ~typ ~expr ~extra_types =
  Lint.check_expr expr;
  Option.iter typ ~f:Lint.check_type;
  let dexp = Desugar.desugar expr in
  Report.display "Desugared" (Pretty.expr dexp);
  let dtyp = Option.map typ ~f:(fun t ->
      let ret = Desugar.desugar_type t in
      Report.display "Desugared type signature" (Pretty.typ ret);
      ret
    )
  in
  let typ_var =
    Typecheck.typecheck
      dexp
      ~want:(Option.to_list dtyp @ extra_types)
      ~get_import_type:(fun _ -> failwith "TODO: imports")
  in
  let typ = Extract.get_var_type typ_var in
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
  {typ; typ_var; rt_expr; js_expr}

let maybe_chop_suffix str suffix =
  let suffix_len = String.length suffix in
  if String.equal (String.suffix str suffix_len) suffix then
    String.prefix str (String.length str - suffix_len)
  else
    str

let load_file () ~base_path ~types =
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
  load_surface_ast () ~typ ~expr ~extra_types:types
