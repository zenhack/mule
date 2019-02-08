
let next = ref 0

let gensym () =
  let result = !next in
  next := result + 1;
  result

let anon_var () =
  Ast.Var ("$" ^ string_of_int (gensym ()))
