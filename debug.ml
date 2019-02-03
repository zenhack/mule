
let todo str =
  print_endline ("TODO: " ^ str);
  exit 1

let impossible msg =
  print_endline ("BUG: " ^ msg);
  exit 1
