open Common_ast
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
  { l with
    tv_id = GT.Ids.Type.min l.tv_id r.tv_id;
    tv_merged = Set.union l.tv_merged r.tv_merged;
  }

let mismatched_kinds ctx merge id lk rk =
  Context.error ctx (`TypeError (`MismatchedKinds(lk, rk)));
  merge (`Poison id)

let mismatched_ctors ctx merge id c lc rc =
    Context.error ctx
      (`TypeError (`UnifyFailed MuleErr.{
            ue_constraint = c;
            ue_cause = `MismatchedCtors (lc, rc);
          }));
    merge (`Poison id)

let rec unify_typ ctx c lv rv =
  unify_vars ctx Context.typ lv rv (fun merge l r ->
    match l, r with
    | `Poison x, _ | _, `Poison x -> merge (`Poison x)
    | `Free ltv, `Free rtv ->
        merge (`Free (merge_tyvar ctx ltv rtv))

    | `Ctor (lid, _), `Ctor (rid, _)
    | `Apply(lid, _, _), `Apply(rid, _, _)
    | `Lambda(lid, _, _), `Lambda(rid, _, _)
      when GT.Ids.Type.equal lid rid ->
        merge l

    | `Free tv, x | x, `Free tv ->
        let bnd = Context.read_var ctx Context.bound tv.tv_bound in
        let report_err flag =
          Context.error ctx
            (`TypeError (`UnifyFailed (MuleErr.{
                  ue_constraint = c;
                  ue_cause = `CantInstantiate (flag, x);
                })));
          merge (`Poison tv.tv_id)
        in
        begin match bnd.b_flag with
          | `Flex -> merge x
          | `Rigid -> report_err `Rigid
          | `Explicit -> report_err `Explicit
        end
    | `Ctor (lid, lc), `Ctor (rid, rc) ->
        merge_ctor ctx c merge (lid, lc) (rid, rc)
    | `Apply(_, lf, larg), `Apply(_, rf, rarg) ->
        unify_quant ctx c lf rf;
        unify_quant ctx c larg rarg;
        merge l
    | `Lambda(_, lp, lbody), `Lambda(_, rp, rbody) ->
        unify_quant ctx c lp rp;
        unify_quant ctx c lbody rbody
    | `GetField(_, lsec, llbl), `GetField(_, rsec, rlbl)
        when Label.equal llbl rlbl && Poly.equal lsec rsec ->
          ()
    | _ ->
        Context.error ctx
          (`TypeError (`UnifyFailed MuleErr.{
                ue_constraint = c;
                ue_cause = failwith "TODO: unify_typ fallthrough (1)";
              }));
        merge (`Poison (failwith "TODO: unify_typ_fallthrough (2)"))
  )
and merge_ctor ctx c merge (lid, lc) (rid, rc) =
  match lc, rc with
  | `Type lt,`Type rt -> merge_type_ctor ctx c merge lid lt rid rt
  | `Row lr,`Row rr -> merge_row_ctor ctx c merge lid lr rid rr
  | `Type _, `Row _ -> mismatched_kinds ctx merge lid `Type `Row
  | `Row _, `Type _ -> mismatched_kinds ctx merge lid `Row `Type
and merge_type_ctor ctx c merge lid lt _rid rt =
  let merge' v = merge (`Ctor(lid, `Type v)) in
  let mismatched () =
    mismatched_ctors ctx merge lid c (`Type lt) (`Type rt)
  in
  match lt, rt with
  | `Fn(lp, lr), `Fn(rp, rr) ->
      unify_quant ctx c lp rp;
      unify_quant ctx c lr rr;
      merge' (`Fn(lp, lr))
  | `Const l, `Const r ->
      if Poly.equal l r then
        merge' (`Const l)
      else
        mismatched ()
  | `Record(lt, lv), `Record(rt, rv) ->
      unify_quant ctx c lt rt;
      unify_quant ctx c lv rv;
      merge' (`Record(lt, lv))
  | `Union l, `Union r ->
      unify_quant ctx c l r;
      merge' (`Union l)
  | _ ->
    mismatched ()
and merge_row_ctor ctx c merge lid lr _rid rr =
  match lr, rr with
  | `Empty, `Empty -> merge (`Ctor(lid, `Row `Empty))
  | `Extend(ll, lh, lt), `Extend(rl, rh, rt) when Poly.equal ll rl ->
      unify_quant ctx c lh rh;
      unify_quant ctx c lt rt;
      merge (`Ctor(lid, `Row(`Extend(ll, lh, lt))))
  | `Extend le, `Extend re ->
      (* Labels don't match, but they might just be out of order; do
         this the hard way, where we have to normalize everything: *)
      merge_unorderd_rows ctx c merge le re
  | `Empty, `Extend _
  | `Extend _, `Empty ->
      mismatched_ctors ctx merge lid c (`Row lr) (`Row rr)
and merge_unorderd_rows ctx c merge le re =
  (* TODO(perf): This is a fallback for when rows aren't already
     sorted the same way -- but especially for the large rows that
     come up with "module" records, this is likely to be a bottlneck,
     since it's O(n * log(n)) in the size of the row, and will likely
     for each field access.

     We should at some point find a way to avoid doing all this work
     just for a single field. Most likely this will involve storing
     the row as a map, rather than converting it to one to unify and
     then back, as we do now.

     Much of this inefficiency is an artifact of following the papers
     closely, which are often designed for easy formal analysis of the
     type system, rather than efficient execution.
  *)

  let lm, lt = build_row_map ctx le in
  let rm, rt = build_row_map ctx re in

  (* First, merge the fields that appear explicitly in the two rows: *)
  let common_fields = ref [] in
  let rec merge_field lbl = function
    | [], [] -> None
    | [], (r::rs) -> Some (`Right (r, rs))
    | (l::ls), [] -> Some (`Left (l, ls))
    | (l::ls), (r::rs) ->
          unify_quant ctx c l r;
          common_fields := (lbl, l) :: !common_fields;
          merge_field lbl (ls, rs)
  in
  let m = Map.merge lm rm ~f:(fun ~key:lbl -> function
      | `Both (ls, rs) -> merge_field lbl (NonEmpty.to_list ls, NonEmpty.to_list rs)
      | `Left ls -> Some (`Left ls)
      | `Right rs -> Some (`Right rs)
    )
  in

  let to_pairs lbl vs = List.map ~f:(fun v -> (lbl, v)) (NonEmpty.to_list vs) in
  let (ls, rs) =
    Map.to_alist m
    |> List.partition_map ~f:(function
      | (lbl, `Left ls) -> Either.First (to_pairs lbl ls)
      | (lbl, `Right rs) -> Either.Second (to_pairs lbl rs)
    )
  in
  (* Now we have lists of fields that are disjoint; they only
     appear in one side or the other. These now need to unify
     with each other, but we can't just recurse, since that
     would send us back here in an infinite loop.

     hypothesis: If either of these lists is non-empty, then
     this is always a type error.

     I'm like 95% sure this works, but need to let it germinate
     a bit... What if both tails are flexible?
  *)
  begin match ls, rs with
  | (_::_), (_::_) -> failwith "TODO: both have more fields, type error"
  | ls, rs ->
      let reattach_fields fs tail =
        List.fold_right fs
          ~init:tail
          ~f:(fun (lbl, h) t ->
            (* The bound doesn't really matter, since the extend is
               inert, but we should probably make sure everything is
               well dominated. Just point it at the same thing as the
               tail. *)

            let bnd =
              (Context.read_var ctx Context.quant t).q_bound
              |> Context.read_var ctx Context.bound
            in
            Context.with_quant ctx bnd (fun _ ->
              let ty_id = GT.Ids.Type.fresh (Context.get_ctr ctx) in
              Context.make_var ctx Context.typ (`Ctor(ty_id, `Row(`Extend(lbl, h, t))))
            )
          )
      in
      let qv = reattach_fields (List.concat ls) lt in
      unify_quant ctx c qv (reattach_fields (List.concat rs) rt);
      let qv = reattach_fields (List.rev !common_fields) qv in

      (* It's a bit gross that we have to fish the body out and give it to
         merge; we should refactor to avoid this. *)
      let q = Context.read_var ctx Context.quant qv in
      let ret = Context.read_var ctx Context.typ (Lazy.force q.q_body) in

      merge ret
  end
and build_row_map ctx e =
  (* Build up a map from label -> nonempty list of fields with that label,
     retaining the order of the fields. The first time we hit something
     that's not an `Extends, we return a pair of (the map, tail)
     [e] is the argument to the `Extend constructor for the first field. *)
  let rec go acc qv =
    let GT.{q_body = tv; _} = Context.read_var ctx Context.quant qv in
    match Context.read_var ctx Context.typ (Lazy.force tv) with
    | `Ctor(_, `Row(`Extend(lbl, h, t))) ->
        go
          (Map.update acc lbl ~f:(function
              | None -> NonEmpty.singleton h
              | Some hs -> NonEmpty.cons h hs
            ))
          t
    | _ ->
        (Map.map ~f:NonEmpty.rev acc, qv)
  in
  let (lbl, h, t) = e in
  go (Map.singleton (module Label) lbl (NonEmpty.singleton h)) t
and unify_quant ctx c lv rv =
  Normalize.whnf_qv ctx lv;
  Normalize.whnf_qv ctx rv;
  unify_vars ctx Context.quant lv rv (fun merge l r ->
    unify_bound ctx l.q_bound r.q_bound;
    unify_typ ctx c (Lazy.force l.q_body) (Lazy.force r.q_body);
    merge {
      l with
      q_id = GT.Ids.Quant.min l.q_id r.q_id;
      q_merged = Set.union l.q_merged r.q_merged;
    }
  )
