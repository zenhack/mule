
let () =
  let src = Sys.argv.(1) in
  let dest = Sys.argv.(2) in
  let src_content = Stdio.In_channel.read_all src in
  let dest_content = "let src = \"" ^ String.escaped src_content ^ "\"" in
  Stdio.Out_channel.write_all dest ~data:dest_content
