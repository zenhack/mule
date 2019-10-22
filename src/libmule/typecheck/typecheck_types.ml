(* types used by the type checker *)

open Common_ast
open Types

type u_kind =
  [ `Free of int
  | `Row
  | `Type
  | `Arrow of k_var * k_var
  ]
and k_var = u_kind UnionFind.var

(* These can be the same physical variables for all type/row kind vars,
 * since their identity has no meaning. *)
let ktype = UnionFind.make `Type
let krow = UnionFind.make `Row

let gen_k: unit -> k_var =
  fun () -> UnionFind.make (`Free (Gensym.gensym ()))

type u_typeconst =
  [ `Named of string
  | `Extend of Label.t
  ]
(* Contents of unification variables: *)
and u_type =
  [ `Free of (tyvar * k_var)
  | `Quant of (int * [`All|`Exist] * int * k_var * u_var)
  | `Const of (int * u_typeconst * (u_var * k_var) list * k_var)
  ]
and bound_ty = [ `Rigid | `Flex | `Explicit ]
and 'a bound =
  { b_ty: bound_ty
  ; b_at: 'a
  }
and tyvar =
  { ty_id: int
  ; ty_flag: bound_ty
  }
and u_var = u_type UnionFind.var

type sign = [ `Pos | `Neg ]

type quantifier = [ `All | `Exist ]

let rec get_kind: u_var -> k_var = fun uv -> match UnionFind.get uv with
  | `Const(_, _, _, k) -> k
  | `Free (_, k) -> k
  | `Quant(_, _, _, _, t) -> get_kind t

let flip_sign = function
  | `Pos -> `Neg
  | `Neg -> `Pos

type subtype_side = [ `Sub | `Super ]

let get_flag: quantifier -> subtype_side -> bound_ty =
  fun q sign-> match q, sign with
    | `All, `Sub -> `Flex
    | `All, `Super -> `Rigid
    | `Exist, `Sub -> `Rigid
    | `Exist, `Super -> `Flex

let get_id = function
  | `Const(ty_id, _, _, _) -> ty_id
  | `Quant(ty_id, _, _, _, _) -> ty_id
  | `Free({ty_id; _}, _) -> ty_id

let rec make_u_kind: Desugared_ast.Kind.t -> u_kind = function
  | `Type -> `Type
  | `Row -> `Row
  | `Arrow(x, y) ->
      `Arrow
        ( UnionFind.make (make_u_kind x)
        , UnionFind.make (make_u_kind y)
        )

(* constructors for common type constants. *)
let const: u_typeconst -> (u_var * k_var) list -> k_var -> u_var =
  fun c args k ->
    UnionFind.make (`Const(Gensym.gensym (), c, args, k))
let const_ty name = const (`Named name) [] ktype
let int = const_ty "int"
let text = const_ty "text"
let char = const_ty "char"
let fn: u_var -> u_var -> u_var = fun param ret ->
  const (`Named "->") [param, ktype; ret, ktype] ktype
let ( **> ) = fn
let union: u_var -> u_var = fun row ->
  const (`Named "|") [row, krow] ktype
let record: u_var -> u_var -> u_var = fun r_types r_values ->
  const (`Named "{...}") [r_types, krow; r_values, krow] ktype
let empty: u_var =
  const (`Named "<empty>") [] krow
let extend: Label.t -> u_var -> u_var -> u_var = fun lbl head tail ->
  const (`Extend lbl) [head, ktype; tail, krow] krow
let apply: u_var -> k_var -> u_var -> k_var -> u_var = fun f fk x xk ->
  begin match UnionFind.get fk with
    | `Arrow(_, rk) ->
        const (`Named "<apply>") [f, fk; x, xk] rk
    | `Free _ ->
        let rk = gen_k () in
        UnionFind.merge (fun _ r -> r) fk (UnionFind.make (`Arrow(xk, rk)));
        const (`Named "<apply>") [f, fk; x, xk] rk
    | k ->
        MuleErr.(
          throw
            (`TypeError
               ( `AppParamArg
               (* FIXME: if presented in an error message this may be confusing, as
                * we don't actually need type -> type, but just some arrow kind.
                *
                * We should find a way to not over-specify the kind.
               *)
               , (`MismatchedKinds
                    ( `Arrow(`Type, `Type)
                    , match k with
                    | `Type -> `Type
                    | `Row -> `Row
                    | _ -> failwith "impossible"
                    )
                 )
               )
            )
        )
  end
let quant : [`All|`Exist] -> k_var -> (u_var -> u_var) -> u_var =
  fun q k mkbody ->
    let q_id = Gensym.gensym () in
    let ty_id = Gensym.gensym () in
    let ty_flag = `Explicit in
    let v = UnionFind.make (`Free({ty_id; ty_flag}, k)) in
    UnionFind.make (`Quant(q_id, q, ty_id, k, mkbody v))

let all : k_var -> (u_var -> u_var) -> u_var =
  fun k mkbody -> quant `All k mkbody

let exist : k_var -> (u_var -> u_var) -> u_var =
  fun k mkbody -> quant `Exist k mkbody

let lambda : k_var -> (u_var -> u_var) -> u_var =
  fun kparam mkbody ->
    let id = Gensym.gensym () in
    let param = UnionFind.make (
      `Free
        ( {ty_id = Gensym.gensym (); ty_flag = `Explicit}
        , kparam
        )
    )
    in
    let body = mkbody param in
    let kbody = get_kind body in
    UnionFind.make
      (`Const
        ( id
        , `Named "<lambda>"
        , [param, kparam; body, kbody]
        , UnionFind.make (`Arrow(kparam, kbody))
        )
      )

type permission = F | R | L | E

type unify_edge =
  | Unify of (reason * u_var * u_var)

let typeconst_eq: u_typeconst -> u_typeconst -> bool = Poly.equal
let perm_eq: permission -> permission -> bool = Poly.equal

let rec sexp_of_u_kind: u_kind -> Sexp.t = function
  | `Free n -> Int.sexp_of_t n
  | `Row -> Sexp.Atom "row"
  | `Type -> Sexp.Atom "type"
  | `Arrow(p, r) -> Sexp.List [sexp_of_kvar p; Sexp.Atom "=>"; sexp_of_kvar r]
and sexp_of_kvar: k_var -> Sexp.t = fun v -> sexp_of_u_kind (UnionFind.get v)
and sexp_of_uvar: IntSet.t -> u_var -> Sexp.t =
  fun seen v -> sexp_of_u_type seen (UnionFind.get v)
and sexp_of_u_typeconst: u_typeconst -> Sexp.t = function
  | `Named n -> Sexp.List [Sexp.Atom "named"; Sexp.Atom n]
  | `Extend l -> Sexp.List [Sexp.Atom "extend"; Sexp.Atom (Label.to_string l)]
and sexp_of_flag: bound_ty -> Sexp.t = function
  | `Flex -> Sexp.Atom "flex"
  | `Rigid -> Sexp.Atom "rigid"
  | `Explicit -> Sexp.Atom "explicit"
and sexp_of_quantifier: quantifier -> Sexp.t = function
  | `All -> Sexp.Atom "all"
  | `Exist -> Sexp.Atom "exist"
and sexp_of_u_type: IntSet.t -> u_type -> Sexp.t = fun seen -> function
  | `Free({ty_id; ty_flag}, k) -> Sexp.List [
      sexp_of_flag ty_flag;
      Int.sexp_of_t ty_id;
      sexp_of_kvar k;
    ]
  | `Const(id, c, args, k) ->
      if Set.mem seen id then
        Sexp.List [Sexp.Atom "const"; Int.sexp_of_t id]
      else
        begin
          let seen' = Set.add seen id in
          Sexp.List [
            Sexp.Atom "const";
            Int.sexp_of_t id;
            sexp_of_u_typeconst c;
            Sexp.List (List.map args ~f:(fun (t, k) -> Sexp.List [
                sexp_of_uvar seen' t;
                sexp_of_kvar k;
              ]));
            sexp_of_kvar k;
          ]
        end
  | `Quant(qid, q, vid, k, body) ->
      if Set.mem seen qid then
        Sexp.List [Sexp.Atom "q"; Int.sexp_of_t qid]
      else begin
        let seen' = Set.add seen qid in
        Sexp.List [
          Sexp.Atom "q";
          Int.sexp_of_t qid;
          sexp_of_quantifier q;
          Int.sexp_of_t vid;
          sexp_of_kvar k;
          sexp_of_uvar seen' body
        ]
      end
