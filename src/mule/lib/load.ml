include Load_t

type loader = {
  results: (string, result, String.comparator_witness) Map.t ref;
  current: string option;
  edges: string Tsort.edge list ref;
}

let new_loader () = {
  results = ref (Map.empty (module String));
  current = None;
  edges = ref [];
}

let maybe_chop_suffix str suffix =
  let suffix_len = String.length suffix in
  if String.equal (String.suffix str suffix_len) suffix then
    String.prefix str (String.length str - suffix_len)
  else
    str


let rec load_surface_ast loader ~typ ~expr ~export ~extra_types =
  Lint.check_expr expr;
  Option.iter typ ~f:(fun (_, t) -> Lint.check_type t);
  let dexp = Desugar.desugar expr in
  Report.display "Desugared" (fun () -> Pretty.expr dexp);
  let dtyp = Option.map typ ~f:(fun (src, t) ->
      let ret = Desugar.desugar_type t in
      Report.display "Desugared type signature" (fun () -> Pretty.typ ret);
      (src, ret)
    )
  in
  let typ_var =
    Typecheck.typecheck
      dexp
      ~want:(Option.to_list dtyp @ extra_types)
      ~export
      ~get_import_type:(fun path ->
        let {typ_var; _} = get_or_load loader path in
        typ_var
      )
  in
  let typ = Extract.get_var_type typ_var in
  Report.display "inferred type"  (fun () -> Pretty.typ typ);
  let rt_expr = lazy (
    To_runtime.translate
      dexp
      ~get_import:(fun path ->
        let {rt_expr; _} = get_or_load loader path in
        Lazy.force rt_expr
      )
  )
  in
  let js_expr =
    lazy (
      let e =
        To_js.translate_expr dexp ~get_import:(fun path ->
          let {var; _} = get_or_load loader path in
          var
        )
      in
      Report.display "Js_pre" (fun () -> Sexp.to_string_hum (Js_pre.sexp_of_expr e));
      let e =
        if Config.no_js_cps () then
          e
        else
          begin
            let cps = Js_pre.cps e in
            Report.display "CPS" (fun () -> Sexp.to_string_hum (Js_pre.sexp_of_expr cps));
            cps
          end
      in
      Js_pre.to_js e
    )
  in
  let var = Gensym.anon_var Gensym.global in
  {typ; typ_var; rt_expr; js_expr; var}
and load_file loader ~base_path ~types ~export =
  load_path
    loader
    ~base_path:(maybe_chop_suffix base_path ".mule")
    ~export
    ~types
and load_path loader ~base_path ~types ~export =
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
      Some (`Msig, parse_all Parser.type_file type_path)
    else
      None
  in
  let result = load_surface_ast loader ~typ ~expr ~extra_types:types ~export in
  (* TODO: normalize the path; right now it's still relative. *)
  loader.results := Map.set !(loader.results) ~key:base_path ~data:result;
  result
and get_or_load loader path =
  let path = Paths.base_filepath path in
  match Map.find !(loader.results) path with
  | Some r -> r
  | None ->
      begin match loader.current with
        | Some current ->
            loader.edges := Tsort.{
                from = current;
                to_ = path;
              } :: !(loader.edges)
        | None -> ()
      end;
      load_path
        { loader with current = Some path }
        ~base_path:path
        ~types:[]
        ~export:true


let load_surface_ast loader ~expr ~extra_types =
  load_surface_ast loader ~typ:None ~expr ~extra_types

let all_files {edges; results; _} =
  Tsort.sort (module String)
    ~nodes:(Map.keys !results)
    ~edges:(!edges)
  |> List.map ~f:(function
    | `Single k -> k
    | `Cycle (k, ks) ->
        MuleErr.bug
          ("Module cycle: " ^ String.concat ~sep:" -> " (k::ks))
  )
  |> List.map ~f:(fun k -> (k, Util.find_exn !results k))
