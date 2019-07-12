
let type_of_string s =
  match MParser.parse_string Parser.typ s () with
  | MParser.Failed (msg, _) -> failwith ("parse failed : " ^ msg)
  | MParser.Success ty -> ty

type runner =
  { want_type : Ast.Surface.Type.t
  ; run : Ast.Runtime.Expr.t -> unit
  }

let by_name =
  Map.empty (module String)
