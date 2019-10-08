let next = ref 0

let gensym () =
  let result = !next in
  next := result + 1;
  result

let anon_var () =
  Common_ast.Var.of_string ("$" ^ Int.to_string (gensym ()))
