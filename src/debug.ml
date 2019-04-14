type edge_type =
  [ `Structural
  | `Unify
  | `Instance
  | `Sibling
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
    fun f -> Stdio.print_endline (f ())
  else
    fun _ -> ()

let frame_no: int ref = ref 0

let edges: (edge_type * int * int) list ref = ref []
let nodes: (node_type * int) list ref = ref []

let start_graph () =
  edges := [];
  nodes := []

let show_edge ty from to_ =
  edges := (ty, from, to_) :: !edges

let show_node ty n =
  nodes := (ty, n) :: !nodes

let root_node: int option ref =
  ref None

let set_root: int -> unit = fun id ->
  root_node := Some id

let fmt_node: node_type -> int -> string =
  fun ty n ->
    String.concat
    [ "  n"
    ; Int.to_string n
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
    ; " : "
    ; Int.to_string n
    ; "\"];\n"
    ]

let fmt_edge_ty = function
  | `Structural -> "[weight=7]"
  | `Unify -> "[color=green, dir=none, constraint=false, weight=4]"
  | `Instance -> "[color=red, constraint=false, weight=4]"
  | `Binding `Flex -> "[style=dotted, dir=back, weight=1]"
  | `Binding `Rigid -> "[style=dashed, dir=back, weight=1]"
  | `Sibling -> "[style=invis, constriant=false]"

module Out = Stdio.Out_channel

let end_graph () =
  let path = Printf.sprintf "/tmp/graph-%03d.dot" !frame_no in
  frame_no := !frame_no + 1;
  let dest = Out.create path in
  Out.fprintf dest "digraph g {\n";
  begin match !root_node with
  | Some id -> Out.fprintf dest "  root=\"n%d\";\n" id
  | None -> ()
  end;
  List.iter !nodes ~f:(fun (ty, id) ->
    Out.fprintf dest "%s" (fmt_node ty id)
  );
  List.iter !edges ~f:(fun (ty, from, to_) ->
    match ty with
    | `Sibling ->
      Out.fprintf dest "  {rank=same; rankdir=LR; n%d -> n%d %s}\n" from to_ (fmt_edge_ty ty)
    | _ ->
      Out.fprintf dest "  n%d -> n%d %s;\n" from to_ (fmt_edge_ty ty)
  );
  Out.fprintf dest "}\n";
  Out.close dest;
  let _ = Caml.Sys.command ("dot -Tsvg " ^ path ^ " -o " ^ path ^ ".svg") in
  let _ = Caml.Sys.command ("firefox " ^ path ^ ".svg") in
  ()
