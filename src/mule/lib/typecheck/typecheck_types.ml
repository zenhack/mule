open Common_ast
include Typecheck_types_t

(* These can be the same physical variables for all type/row kind vars,
 * since their identity has no meaning. *)
let ktype = UnionFind.make `Type
let krow = UnionFind.make `Row

let gen_k: unit -> k_var =
  fun () -> UnionFind.make (`Free (Gensym.gensym ()))

let rec get_kind: u_var -> k_var = fun uv -> match UnionFind.get uv with
  | `Const(_, _, _, k) -> k
  | `Free {ty_kind; _} -> ty_kind
  | `Bound {bv_kind; _} -> bv_kind
  | `Quant {q_body; _} -> get_kind q_body

let flip_sign = function
  | `Pos -> `Neg
  | `Neg -> `Pos

type unify_dir = [ `Narrow | `Widen ]

let get_flag: quantifier -> unify_dir -> bound_ty =
  fun q sign-> match q, sign with
    | `All, `Narrow -> `Flex
    | `All, `Widen -> `Rigid
    | `Exist, `Narrow -> `Rigid
    | `Exist, `Widen -> `Flex

let get_id = function
  | `Const(ty_id, _, _, _) -> ty_id
  | `Quant {q_id; _} -> q_id
  | `Free{ty_id; _} -> ty_id
  | `Bound {bv_id; _} -> bv_id

let rec make_u_kind: Desugared_ast.Kind.t -> u_kind = function
  | `Type -> `Type
  | `Row -> `Row
  | `Arrow(x, y) ->
      `Arrow
        ( UnionFind.make (make_u_kind x)
        , UnionFind.make (make_u_kind y)
        )

let top_or_bottom_q = function
  | `Quant {q_quant; q_var = {bv_id; _}; q_body; _} ->
      begin match UnionFind.get q_body with
        | `Bound{bv_id = bv_id'; _} when bv_id = bv_id' -> Some q_quant
        | _ -> None
      end
  | _ -> None

let is_top_or_bottom t =
  Option.is_some (top_or_bottom_q t)

let is_top t = match top_or_bottom_q t with
  | Some `Exist -> true
  | _ -> false

let is_bottom t = match top_or_bottom_q t with
  | Some `All -> true
  | _ -> false

(* constructors for common type constants. *)
let const: u_typeconst -> (u_var * k_var) list -> k_var -> u_var =
  fun c args k ->
  UnionFind.make (`Const(Gensym.gensym (), c, args, k))
let const_ty name = const (`Named name) [] ktype
let int = const_ty `Int
let text = const_ty `Text
let char = const_ty `Char
let fn: u_var -> u_var -> u_var = fun param ret ->
  const (`Named `Fn) [param, ktype; ret, ktype] ktype
let ( **> ) = fn
let union: u_var -> u_var = fun row ->
  const (`Named `Union) [row, krow] ktype
let record: u_var -> u_var -> u_var = fun r_types r_values ->
  const (`Named `Record) [r_types, krow; r_values, krow] ktype
let extend: Label.t -> u_var -> u_var -> u_var = fun lbl head tail ->
  const (`Extend lbl) [head, ktype; tail, krow] krow
let apply: u_var -> u_var -> u_var = fun f x ->
  let fk = get_kind f in
  let xk = get_kind x in
  begin match UnionFind.get fk with
    | `Arrow(_, rk) ->
        const (`Named `Apply) [f, fk; x, xk] rk
    | `Free _ ->
        let rk = gen_k () in
        UnionFind.merge (fun _ r -> r) fk (UnionFind.make (`Arrow(xk, rk)));
        const (`Named `Apply) [f, fk; x, xk] rk
    | k ->
        MuleErr.throw
          (`TypeError
              (* FIXME: if presented in an error message this may be confusing, as
               * we don't actually need type -> type, but just some arrow kind.
               *
               * We should find a way to not over-specify the kind.
              *)
              (`MismatchedKinds
                  ( `Arrow(`Type, `Type)
                  , match k with
                  | `Type -> `Type
                  | `Row -> `Row
                  | _ -> failwith "impossible"
                  )
              )
          )
  end
let recur : ident:var_ident -> (u_var -> u_var) -> u_var = fun ~ident mkbody ->
  let ty_id = Gensym.gensym () in
  let v = UnionFind.make (`Bound {
      bv_id = ty_id;
      bv_info = {vi_ident = ident; vi_binder = Some `Rec};
      bv_kind = ktype;
    })
  in
  let body = mkbody v in
  UnionFind.merge (fun _ r -> r) v body;
  body
let quant : ident:var_ident -> [`All|`Exist] -> k_var -> (u_var -> u_var) -> u_var =
  fun ~ident q k mkbody ->
  let q_id = Gensym.gensym () in
  let ty_id = Gensym.gensym () in
  let bv = {
    bv_id = ty_id;
    bv_info = {
      vi_ident = ident;
      vi_binder = Some (`Quant q);
    };
    bv_kind =  k;
  }
  in
  let v = UnionFind.make (`Bound bv) in
  UnionFind.make (`Quant {
      q_id;
      q_quant = q;
      q_var = bv;
      q_kind = k;
      q_body = mkbody v;
    })

let all : ident:var_ident -> k_var -> (u_var -> u_var) -> u_var =
  fun ~ident k mkbody -> quant ~ident `All k mkbody

let exist : ident:var_ident -> k_var -> (u_var -> u_var) -> u_var =
  fun ~ident k mkbody -> quant ~ident `Exist k mkbody

let empty_record_vals: u_var =
  exist ~ident:`EmptyRecordVals krow (fun r -> r)

let empty_record_types: u_var =
  all ~ident:`EmptyRecordTypes krow (fun r -> r)

let empty_union: u_var =
  all ~ident:`EmptyUnion krow (fun r -> r)

let some_union: u_var =
  exist ~ident:`SomeUnion krow (fun r -> r)

let lambda : ident:var_ident -> k_var -> (u_var -> u_var) -> u_var =
  fun ~ident kparam mkbody ->
  let id = Gensym.gensym () in
  let param = UnionFind.make (`Bound {
      bv_id = Gensym.gensym();
      bv_info = {
        vi_ident = ident;
        vi_binder = Some `Lambda;
      };
      bv_kind = kparam;
    })
  in
  let body = mkbody param in
  let kbody = get_kind body in
  UnionFind.make
    (`Const
        ( id
        , `Named `Lambda
        , [param, kparam; body, kbody]
        , UnionFind.make (`Arrow(kparam, kbody))
        )
    )

let rec sexp_of_u_kind: u_kind -> Sexp.t = function
  | `Free n -> Int.sexp_of_t n
  | `Row -> Sexp.Atom "row"
  | `Type -> Sexp.Atom "type"
  | `Arrow(p, r) -> Sexp.List [sexp_of_kvar p; Sexp.Atom "=>"; sexp_of_kvar r]
and sexp_of_kvar: k_var -> Sexp.t = fun v -> sexp_of_u_kind (UnionFind.get v)
and sexp_of_uvar: (int, Int.comparator_witness) Set.t -> u_var -> Sexp.t =
  fun seen v -> sexp_of_u_type seen (UnionFind.get v)
and sexp_of_u_typeconst: u_typeconst -> Sexp.t = function
  | `Named n -> Sexp.List [Sexp.Atom "named"; sexp_of_typeconst_name n]
  | `Extend l -> Sexp.List [Sexp.Atom "extend"; Sexp.Atom (Label.to_string l)]
and sexp_of_flag: bound_ty -> Sexp.t = function
  | `Flex -> Sexp.Atom "flex"
  | `Rigid -> Sexp.Atom "rigid"
and sexp_of_quantifier: quantifier -> Sexp.t = function
  | `All -> Sexp.Atom "all"
  | `Exist -> Sexp.Atom "exist"
and sexp_of_u_type: (int, Int.comparator_witness) Set.t -> u_type -> Sexp.t = fun seen -> function
  | `Free {ty_id; ty_flag; ty_scope; ty_kind; _} -> Sexp.List [
      sexp_of_flag ty_flag;
      Int.sexp_of_t ty_id;
      Scope.sexp_of_t ty_scope;
      sexp_of_kvar ty_kind;
    ]
  | `Bound{bv_id = id; bv_kind = k; _} ->
      Sexp.List [
        Sexp.Atom "bound";
        Int.sexp_of_t id;
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
  | `Quant {q_id = qid; q_quant = q; q_var = {bv_id = vid; _}; q_kind = k; q_body = body} ->
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
