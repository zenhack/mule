
type edge_type =
  [ `Structural
  | `Unify
  | `Instance
  | `Binding of [ `Flex | `Rigid ]
  ]
type node_type =
  [ `TyVar
  | `TyFn
  | `TyRecord
  | `TyUnion
  | `RowVar
  | `RowEmpty
  | `RowExtend of Ast.Label.t
  | `G
  ]

let report enabled =
  if enabled then
    fun f -> print_endline (f ())
  else
    fun _ -> ()

let edges: (edge_type * int * int) list ref = ref []
let nodes: (node_type * int) list ref = ref []

let start_graph () =
  edges := [];
  nodes := []

let show_edge ty from to_ =
  edges := (ty, from, to_) :: !edges

let show_node ty n =
  nodes := (ty, n) :: !nodes

let fmt_node: node_type -> int -> string =
  fun ty n ->
    String.concat ""
    [ "  n"
    ; string_of_int n
    ; " [label=\""
    ; begin match ty with
      | `TyVar -> "T"
      | `TyFn -> "->"
      | `TyRecord -> "{}"
      | `TyUnion -> "|"
      | `RowVar -> "R"
      | `RowEmpty -> "Nil"
      | `RowExtend lbl -> Ast.Label.to_string lbl ^ " ::"
      | `G -> "G"
      end
    ; "\"];\n"
    ]

let fmt_edge_ty = function
  | `Structural -> ""
  | `Unify -> "[color=green, dir=none]"
  | `Instance -> "[color=red]"
  | `Binding `Flex -> "[style=dotted, dir=back]"
  | `Binding `Rigid -> "[style=dashed, dir=back]"

let end_graph () =
  let path = "/tmp/graph.dot" in
  let dest = open_out path in
  Printf.fprintf dest "digraph g {\n";
  !nodes |> List.iter
    (fun (ty, id) ->
      Printf.fprintf dest "%s" (fmt_node ty id));
  !edges |> List.iter
    (fun (ty, from, to_) ->
      Printf.fprintf dest "  n%d -> n%d %s;\n" from to_ (fmt_edge_ty ty));
  Printf.fprintf dest "}\n";
  close_out dest;
  let _ = Sys.command ("xdot " ^ path) in
  ()
