let build src dest =
  let dest = match dest with
    | Some d -> d
    | None -> src ^ ".js"
  in
  let Load.{js_expr; _} =
    Load.load_file (Load.new_loader ()) ~base_path:src ~types:[]
  in
  let text =
    Lazy.force js_expr
    |> Js_ast.expr
    |> Fmt.(fun e -> concat [
        s "const mule = (() => {";
        s Js_runtime_gen.src; s "\n";
        s "mule.main = "; e; s "\n";
        s "return mule\n";
        s "})()\n";
      ])
    |> Fmt.to_string
  in
  Stdio.Out_channel.write_all dest ~data:text
