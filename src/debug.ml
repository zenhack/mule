
let report enabled =
  if enabled then
    fun f -> print_endline (f ())
  else
    fun _ -> ()
