(* types used by the type checker *)

type u_kind =
  [ `Row
  | `Type
  ]

type u_typeconst =
  [ `Named of string
  | `Extend of Ast.Label.t
  ]
(* Contents of unification variables: *)
and u_type =
  [ `Free of (tyvar * u_kind)
  | `Const of (tyvar * u_typeconst * (u_type UnionFind.var * u_kind) list * u_kind)
  ]
and bound_ty = [ `Rigid | `Flex ]
and 'a bound =
  { b_ty: bound_ty
  ; b_at: 'a
  }
and tyvar =
  { ty_id: int
  ; ty_bound: bound_target bound ref
  }
and g_node =
  { g_id: int
  ; g_bound: (g_node bound) option
  ; g_child: u_type UnionFind.var Lazy.t
  }
and bound_target =
  [ `Ty of u_type UnionFind.var Lazy.t
  | `G of g_node
  ]

(* constructors for common type constants. *)
let int tv = `Const(tv, `Named "int", [], `Type)
let fn tv param ret = `Const(tv, `Named "->", [param, `Type; ret, `Type], `Type)
let union tv row = `Const(tv, `Named "|", [row, `Row], `Type)
let record tv r_types r_values= `Const(tv, `Named "{...}", [r_types, `Row; r_values, `Row], `Type)
let empty tv = `Const(tv, `Named "<empty>", [], `Row)
let extend tv lbl head tail = `Const(tv, `Extend lbl, [head, `Type; tail, `Row], `Row)

type permission = F | R | L

type unify_edge =
  | Unify of (u_type UnionFind.var * u_type UnionFind.var)

type inst_edge =
  { ie_g_node: g_node
  ; ie_ty_node: u_type UnionFind.var
  }

let typeconst_eq: u_typeconst -> u_typeconst -> bool = Poly.equal
let perm_eq: permission -> permission -> bool = Poly.equal

let get_tyvar: u_type -> tyvar = function
  | `Free (v, _) -> v
  | `Const (v, _, _, _) -> v
let get_u_bound x = !((get_tyvar x).ty_bound)

let rec show_u_type_v s v =
  let t = UnionFind.get v in
  let n = (get_tyvar t).ty_id in
  if Set.mem s n then
    "t" ^ Int.to_string n
  else
    let s = Set.add s n in
    match t with
    | `Free _ -> "t" ^ Int.to_string n
    | `Const (_, c, args, _) ->
        begin match c, args with
        | `Named "->", [l, _; r, _] ->
            "(" ^ show_u_type_v s l ^ " -> " ^ show_u_type_v s r ^ ")"
        | `Named "{...}", [row, _] ->
            "Record{" ^ show_u_type_v s row ^ "}"
        | `Named "|", [row, _] ->
            "Union(" ^ show_u_type_v s row ^ ")"
        | `Named name, [] -> name
        | `Named name, _ -> String.concat
            [ name
            ; "("
            ; List.map args ~f:(fun (ty, _kind) -> show_u_type_v s ty)
              |> String.concat ~sep:", "
            ; ")"
            ]
        | `Extend lbl, [head, _; tail, _] ->
            String.concat
              [ "("
              ; Ast.Label.to_string lbl
              ; " => "
              ; show_u_type_v s head
              ; ") :: "
              ; show_u_type_v s tail
              ]
        | `Extend _, _ ->
            failwith "BUG: wrong number of args."
        end
let show_u_type_v: u_type UnionFind.var -> string = show_u_type_v IntSet.empty

let show_g {g_child; _} =
  show_u_type_v (Lazy.force g_child)
