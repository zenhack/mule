module GT = Graph_types

let rec pk_occurs_in_kind ctx id kv =
  let GT.{k_prekind; _} = Context.read_var ctx Context.kind kv in
  pk_occurs_in_prekind_v ctx id k_prekind
and pk_occurs_in_prekind_v ctx id pkv =
  pk_occurs_in_prekind ctx id (Context.read_var ctx Context.prekind pkv)
and pk_occurs_in_prekind ctx id = function
  | `Free id' -> GT.Ids.Kind.equal id id'
  | `Arrow (p, r) -> pk_occurs_in_kind ctx id p || pk_occurs_in_kind ctx id r
  | `Type | `Row | `Poison -> false

let unify_vars ctx vtype lv rv unify_vals =
  if not (Context.var_eq ctx vtype lv rv) then
    begin
      let read var = Context.read_var ctx vtype var in
      let merge value = Context.merge ctx vtype lv rv value in
      let l = read lv in
      let r = read rv in
      unify_vals merge l r
    end

let unify_guard ctx lv rv =
  unify_vars ctx Context.guard lv rv (fun merge l r ->
    match l, r with
    | `Poison, _ | _, `Poison -> merge `Poison
    | `Guarded, `Guarded
    | `Unguarded, `Unguarded
    | _, `Free ->
        merge l
    | `Free, _ ->
        merge r
    | `Guarded, `Unguarded
    | `Unguarded, `Guarded ->
        Context.error ctx (`TypeError `MismatchedGuards);
        merge `Poison
  )

let rec unify_kind ctx lv rv =
  unify_vars ctx Context.kind lv rv (fun merge l r ->
    unify_prekind ctx l.k_prekind r.k_prekind;
    unify_guard ctx l.k_guard r.k_guard;
    merge l
  )
and unify_prekind ctx lv rv =
  unify_vars ctx Context.prekind lv rv (fun merge l r ->
    match l, r with
    | `Poison, _ | _, `Poison -> merge `Poison
    | `Row, `Row | `Type, `Type -> merge l
    | `Free id, other | other, `Free id ->
        if pk_occurs_in_prekind ctx id other then
          begin
            Context.error ctx (`TypeError `OccursCheckKind);
            merge `Poison
          end
        else
          merge other
    | `Arrow(p, r), `Arrow(p', r') ->
        unify_kind ctx p p';
        unify_kind ctx r r'
    | _ ->
        let rec extract_prekind = function
          | `Poison -> `Unknown
          | `Free _ -> `Unknown
          | `Row -> `Row
          | `Type -> `Type
          | `Arrow(p, r) -> `Arrow(extract_kind p, extract_kind r)
        and extract_kind kv =
          let GT.{k_prekind; _} = Context.read_var ctx Context.kind kv in
          extract_prekind (Context.read_var ctx Context.prekind k_prekind)
        in
        Context.error ctx (`TypeError (`MismatchedKinds(extract_prekind l, extract_prekind r)));
        merge `Poison
  )

(*
open Common_ast
open Graph_types

type error =
  [ `CtorMismatch of (ctor * ctor)
  ]

type type_path =
  [ `Fn of [ `Param | `Result ]
  | `Extend of Label.t * [ `Head | `Tail ]
  | `Record of [ `Types | `Values ]
  ]

module Context : sig
  type t

  val error : typ var -> typ var -> error -> t -> unit

  val walk : type_path -> t -> t
end = struct
  type t = unit
  let error l r _ _ =
    UnionFind.merge (fun _ _ -> `Poison) l r;
    failwith "TODO: errors."
  let walk _ ctx = ctx
end


let rec unify_typ ctx l r =
  Union_find.modify Normalize.whnf_typ l;
  Union_find.modify Normalize.whnf_typ r;
  if UnionFind.equal l r then
    l
  else
    begin match UnionFind.get l, UnionFind.get r with
      | `Poison, _ | _, `Poison ->
          UnionFind.merge (fun _ _ -> `Poison) l r
      | `Ctor cl, `Ctor cr ->
          unfiy_ctor ctx l cl r cr
    end
and unify_ctor ctx l cl r cr =
  match cl, cr with
  | `Type tl, `Type tr ->
      unify_type_ctor ctx l tl r tr
  | `Row rl, `Row rr ->
      unify_row_ctor ctx l rl r rr
  (* TODO: other cases; shouldn't happen, but we should panic explicitly. *)
and unify_type_ctor ctx l tl r tr =
  match tl, tr with
  | `Const x, `Const y ->
      if Poly.equal x y then
        UnionFind.merge (fun _ r -> r) l r
      else
        Context.error l r (`CtorMismatch (`Type (`Const tl), `Type (Const tr))) ctx
  (* TODO: other variants *)
and unify_row_ctor ctx l rl r rr =
  match rl, rr with
  | `Empty, `Empty ->
      UnionFind.merge (fun _ r -> r) l r
  (* TODO: `Extend *)
*)
