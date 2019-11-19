
let print_ p s =
  p s;
  Stdio.Out_channel.flush Stdio.stdout

let print_string s =
  print_ Stdio.print_string s

let print_endline s =
  print_ Stdio.print_endline s

let display_always label text =
  let text =
    String.split_lines text
    |> List.map ~f:(fun line -> "\t" ^ line)
    |> String.concat ~sep:"\n"
  in
  print_endline ("\n" ^ label ^ ":\n\n" ^ text)

let display label text =
  if Config.debug_steps () then
    display_always label (text ())
