
let next = ref 0

let gensym () =
  let result = !next in
  next := result + 1;
  result
