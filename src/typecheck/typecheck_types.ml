(* types used by the type checker *)

type u_kind =
  [ `Free of int
  | `Row
  | `Type
  | `Arrow of k_var * k_var
  ]
and k_var = u_kind UnionFind.var

(* These can be the same physical variables for all type/row kind vars,
 * since their identity has no meaning. *)
let kvar_type = UnionFind.make `Type
let kvar_row = UnionFind.make `Row

let gen_k: unit -> k_var =
  fun () -> UnionFind.make (`Free (Gensym.gensym ()))

type u_typeconst =
  [ `Named of string
  | `Extend of Ast.Label.t
  ]
(* Contents of unification variables: *)
and u_type =
  [ `Free of (tyvar * k_var)
  | `Quant of (tyvar * u_type UnionFind.var)
  | `Const of (tyvar * u_typeconst * (u_type UnionFind.var * k_var) list * k_var)
  ]
and bound_ty = [ `Rigid | `Flex | `Explicit ]
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

type u_var = u_type UnionFind.var

type sign = [ `Pos | `Neg ]

type quantifier = [ `All | `Exist ]

let rec get_kind: u_var -> k_var = fun uv -> match UnionFind.get uv with
  | `Const(_, _, _, k) -> k
  | `Free (_, k) -> k
  | `Quant(_, t) -> get_kind t

let flip_sign = function
  | `Pos -> `Neg
  | `Neg -> `Pos

let get_flag: quantifier -> sign -> bound_ty =
  fun q sign-> match q, sign with
    | `All, `Pos -> `Flex
    | `All, `Neg -> `Rigid
    | `Exist, `Pos -> `Rigid
    | `Exist, `Neg -> `Flex

let rec make_u_kind: Ast.Desugared.Kind.t -> u_kind = function
  | `Type -> `Type
  | `Row -> `Row
  | `Arrow(x, y) ->
      `Arrow
        ( UnionFind.make (make_u_kind x)
        , UnionFind.make (make_u_kind y)
        )

(* constructors for common type constants. *)
let int: tyvar -> u_type = fun tv ->
  `Const(tv, `Named "int", [], kvar_type)
let text: tyvar -> u_type = fun tv ->
  `Const(tv, `Named "text", [], kvar_type)
let fn: tyvar -> u_var -> u_var -> u_type = fun tv param ret ->
  `Const(tv, `Named "->", [param, kvar_type; ret, kvar_type], kvar_type)
let union: tyvar -> u_var -> u_type = fun tv row ->
  `Const(tv, `Named "|", [row, kvar_row], kvar_type)
let record: tyvar -> u_var -> u_var -> u_type = fun tv r_types r_values ->
  `Const(tv, `Named "{...}", [r_types, kvar_row; r_values, kvar_row], kvar_type)
let empty: tyvar -> u_type = fun tv ->
  `Const(tv, `Named "<empty>", [], kvar_row)
let extend: tyvar -> Ast.Label.t -> u_var -> u_var -> u_type = fun tv lbl head tail ->
  `Const(tv, `Extend lbl, [head, kvar_type; tail, kvar_row], kvar_row)
let witness: tyvar -> k_var -> u_var -> u_type = fun tv kind ty ->
  `Const(tv, `Named "<witness>", [ty, kind], kvar_type)
let apply: tyvar -> u_var -> k_var -> u_var -> k_var -> u_type = fun tv f fk x xk ->
  begin match UnionFind.get fk with
    | `Arrow(_, rk) ->
        `Const(tv, `Named "<apply>", [f, fk; x, xk], rk)
    | `Free _ ->
        let rk = gen_k () in
        UnionFind.merge (fun _ r -> r) fk (UnionFind.make (`Arrow(xk, rk)));
        `Const(tv, `Named "<apply>", [f, fk; x, xk], rk)
    | k ->
        raise MuleErr.(
            MuleExn
              (TypeError (MismatchedKinds
                            ( `Arrow(`Type, `Type)
                            , match k with
                            | `Type -> `Type
                            | `Row -> `Row
                            | _ -> failwith "impossible"
                            )
                         ))
          )
  end

type permission = F | R | L | E

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
  | `Quant (v, _) -> v
let get_u_bound x = !((get_tyvar x).ty_bound)
