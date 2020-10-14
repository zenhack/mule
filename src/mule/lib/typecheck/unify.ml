

let unify_guard ctx lv rv =
  if not (Context.var_eq ctx Context.guard lv rv) then
    begin
      let read var = Context.read_var ctx Context.guard var in
      let merge value = Context.merge ctx Context.guard lv rv value in
      let l = read lv in
      let r = read rv in
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
    end
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
