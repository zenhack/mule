module Var = Common_ast.Var

let build src dest =
  let dest = match dest with
    | Some d -> d
    | None -> src ^ ".js"
  in
  let loader = Load.new_loader () in
  let Load.{var = main_var; _} =
    Load.load_file loader ~base_path:src ~types:[]
  in
  let files =
    Load.all_files loader
    |> List.map ~f:(fun (_, Load.{var; js_expr; _}) ->
      Js_ast.VarDecl(Var.to_string var, Lazy.force js_expr)
    )
    |> Js_ast.stmts
  in
  let text =
    Fmt.(concat [
        s "const mule = (() => {";
        s Js_runtime_gen.src; s "\n";
        files;
        s "mule.main = () => $exec(";
        s (Var.to_string main_var);
        s ", $js, globalThis)\n";
        s "return mule\n";
        s "})()\n";
        s "mule.main();\n"
      ])
    |> Fmt.to_string
  in
  Stdio.Out_channel.write_all dest ~data:text
