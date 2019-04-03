(* types used by the type checker *)

(* Contents of unification variables for types: *)
type u_type =
  [ `Free of tyvar
  | `Fn of (tyvar * u_type UnionFind.var * u_type UnionFind.var)
  | `Record of (tyvar * u_row UnionFind.var)
  | `Union of (tyvar * u_row UnionFind.var)
  ]
(* ...and rows: *)
and u_row =
  [ `Free of tyvar
  | `Extend of (tyvar * Ast.Label.t * u_type UnionFind.var * u_row UnionFind.var)
  | `Empty of tyvar
  ]
and bound_ty = [ `Rigid | `Flex ]
and 'a bound =
  { b_ty: bound_ty
  ; b_at: 'a
  }
and tyvar =
  { ty_id: int
  ; ty_bound: bound_target bound UnionFind.var
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

type permission = F | R | L

let perm_eq: permission -> permission -> bool = Poly.equal

(* Get the "permission" of a node, based on the node's binding path
 * (starting from the node and working up the tree). See section 3.1
 * in {MLF-Graph-Unify}. *)
let rec get_permission: bound_ty list -> permission = function
  | [] -> F
  | (`Rigid :: _) -> R
  | (`Flex :: bs) ->
      begin match get_permission bs with
        | F -> F
        | R | L -> L
      end

let rec gnode_bound_list {g_bound; _} = match g_bound with
  | None -> []
  | Some {b_ty; b_at} -> b_ty :: gnode_bound_list b_at
let get_tyvar: [< u_type | u_row ] -> tyvar = function
  | `Free v -> v
  | `Fn (v, _, _) -> v
  | `Record (v, _) -> v
  | `Union (v, _) -> v
  | `Extend(v, _, _, _) -> v
  | `Empty v -> v
let get_u_bound x = UnionFind.get (get_tyvar x).ty_bound

let rec show_u_type_v s v =
  let t = UnionFind.get v in
  let n = (get_tyvar t).ty_id in
  if Set.mem s n then
    "t" ^ Int.to_string n
  else
    let s = Set.add s n in
    match t with
    | `Free _ -> "t" ^ Int.to_string n
    | `Fn (_, l, r) ->
        "(" ^ show_u_type_v s l ^ " -> " ^ show_u_type_v s r ^ ")"
    | `Record(_, row) ->
        "Record{" ^ show_u_row_v s row ^ "}"
    | `Union(_, row) ->
        "Union(" ^ show_u_row_v s row ^ ")"
and show_u_row_v s v =
  let r = UnionFind.get v in
  let n = (get_tyvar r).ty_id in
  if Set.mem s n then
    "r" ^ Int.to_string n
  else
    let s = Set.add s n in
    match r with
    | `Free {ty_id; _} ->
        "r" ^ Int.to_string ty_id
    | `Empty _ ->
        "<empty>"
    | `Extend (_, lbl, ty, rest) ->
        "(" ^ Ast.Label.to_string lbl ^ " => " ^ show_u_type_v s ty ^ ") :: " ^ show_u_row_v s rest
let show_u_type_v: u_type UnionFind.var -> string = show_u_type_v (Set.empty (module Int))
let show_u_row_v: u_row UnionFind.var -> string = show_u_row_v  (Set.empty (module Int))

let show_g {g_child; _} =
  show_u_type_v (Lazy.force g_child)
