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


let weakest_flag l r = match l, r with
  | `Flex, x | x, `Flex -> x
  | `Rigid, `Rigid -> `Rigid
  | `Explicit, `Explicit -> `Explicit
  | `Rigid, `Explicit | `Explicit, `Rigid ->
      failwith "TODO: poison for flags"

let rec bound_lca ctx l r =
  let order_by_age cmp l r =
    if cmp <= 0 then
      (l, r)
    else
      (r, l)
  in
  match l, r with
  | `G g, `Q qv | `Q qv, `G g ->
      let q = Context.read_var ctx Context.quant qv in
      let b = Context.read_var ctx Context.bound q.q_bound in
      bound_lca ctx (`G g) (b.b_target)
  | `G lg, `G rg ->
      let cmp = GT.Ids.G.compare (GT.GNode.id lg) (GT.GNode.id rg) in
      if cmp = 0 then
        `G lg
      else
        let (older, newer) = order_by_age cmp lg rg in
        bound_lca ctx (`G older) (`G (Option.value_exn (GT.GNode.bound newer)))
  | `Q lqv, `Q rqv ->
      let lq = Context.read_var ctx Context.quant lqv in
      let rq = Context.read_var ctx Context.quant rqv in
      let cmp = GT.Ids.Quant.compare lq.q_id rq.q_id in
      if cmp = 0 then
        `Q lqv
      else
        let ((oqv, _oq), (_nqv, nq)) = order_by_age cmp (lqv, lq) (rqv, rq) in
        let b = Context.read_var ctx Context.bound nq.q_bound in
        bound_lca ctx (`Q oqv) b.b_target

let unify_bound ctx lv rv =
  unify_vars ctx Context.bound lv rv (fun merge l r ->
    merge GT.{
      b_flag = weakest_flag l.b_flag r.b_flag;
      b_target = bound_lca ctx l.b_target r.b_target;
    }
  )

let merge_tyvar ctx l r =
  unify_bound ctx l.GT.tv_bound r.GT.tv_bound;
  unify_kind ctx l.GT.tv_kind r.GT.tv_kind;
  (* TODO: we probably need to track both ids for the later steps of rebind; consider
     making tv_id a set or something. *)
  l

let mismatched_kinds ctx merge id lk rk =
  Context.error ctx (`TypeError (`MismatchedKinds(lk, rk)));
  merge (`Poison id)

let rec unify_typ ctx lv rv =
  unify_vars ctx Context.typ lv rv (fun merge l r ->
    let l = Normalize.whnf_typ ctx l in
    let r = Normalize.whnf_typ ctx r in
    match l, r with
    | `Poison x, _ | _, `Poison x -> merge (`Poison x)
    | `Free ltv, `Free rtv ->
        merge (`Free (merge_tyvar ctx ltv rtv))

    | `Ctor (lid, _), `Ctor (rid, _)
    | `Apply(lid, _, _), `Apply(rid, _, _)
    | `Lambda(lid, _, _), `Lambda(rid, _, _)
      when GT.Ids.Type.equal lid rid ->
        merge l

    | `Ctor (lid, lc), `Ctor (rid, rc) ->
        merge_ctor ctx merge (lid, lc) (rid, rc)
    | `Apply(_, lf, larg), `Apply(_, rf, rarg) ->
        unify_quant ctx lf rf;
        unify_quant ctx larg rarg;
        merge l
    | `Lambda(_, lp, lbody), `Lambda(_, rp, rbody) ->
        unify_quant ctx lp rp;
        unify_quant ctx lbody rbody
    | _ ->
        Context.error ctx (`TypeError (`MismatchedCtors (failwith "TODO")));
        merge (`Poison (failwith "TODO"))
  )
and merge_ctor ctx merge (lid, lc) (rid, rc) =
  match lc, rc with
  | `Type lt,`Type rt -> merge_type_ctor merge lid lt rid rt
  | `Row lr,`Row rr -> merge_row_ctor merge lid lr rid rr
  | `Type _, `Row _ -> mismatched_kinds ctx merge lid `Type `Row
  | `Row _, `Type _ -> mismatched_kinds ctx merge lid `Row `Type
and merge_type_ctor _merge _lid _lt _rid _rt =
  failwith "TODO: merge_type_ctor"
and merge_row_ctor merge lid lr _rid rr =
  match lr, rr with
  | `Empty, `Empty -> merge (`Ctor(lid, `Row `Empty))
  | _ -> failwith "TODO: merge_row_ctor"
and unify_quant ctx lv rv =
  unify_vars ctx Context.quant lv rv (fun merge l r ->
    unify_bound ctx l.q_bound r.q_bound;
    unify_typ ctx (Lazy.force l.q_body) (Lazy.force r.q_body);
    merge l
  )
