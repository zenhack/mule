type counter = unit

let next = ref 0

let global = ()

let gensym () =
  let result = !next in
  next := result + 1;
  result

let anon_var () =
  Common_ast.Var.of_string ("$" ^ Int.to_string (gensym ()))
