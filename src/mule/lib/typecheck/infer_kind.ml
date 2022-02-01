module GT = Graph_types
module C = Constraint_t

let kwithg ctx guard pkv = Context.make_var ctx Context.kind GT.{
    k_prekind = pkv;
    k_guard = Context.make_var ctx Context.guard guard;
  }

let rec infer_kind : Context.t -> GT.typ GT.var -> GT.kind GT.var =
  fun ctx t ->
    let t = Context.read_var ctx Context.typ t in
    match t with
    | `Free tv -> tv.GT.tv_kind
    | `Ctor (_, ctor) -> infer_kind_ctor ctx ctor
    | `Poison _ -> Context.make_var ctx Context.kind GT.{
        k_prekind = Context.make_var ctx Context.prekind `Poison;
        k_guard = Context.make_var ctx Context.guard `Poison;
      }
    | `Lambda(_, p, r) ->
        let k_p = infer_kind_q ctx p in
        let k_r = infer_kind_q ctx r in
        Context.make_var ctx Context.kind GT.{
            k_prekind = Context.make_var ctx Context.prekind (`Arrow(k_p, k_r));
            k_guard = Context.make_var ctx Context.guard `Free;
          }
    | `Apply(_, f, arg) ->
        let k_f = infer_kind_q ctx f in
        let k_arg = infer_kind_q ctx arg in
        let k_ret = kwithg ctx `Free (Context.make_var ctx Context.prekind (`Free(GT.Ids.Kind.fresh (Context.get_ctr ctx)))) in
        let k_f' = kwithg ctx `Free (Context.make_var ctx Context.prekind (`Arrow(k_arg, k_ret))) in
        Context.constrain ctx (`UnifyKind C.{
            unify_kind_sub = k_f;
            unify_kind_super = k_f';
            unify_kind_why = `Apply;
          });
        k_f
    | `Fix _ ->
        (* (unguarded 'k -> guarded 'k) -> guarded 'k,
           where the arrows' guards are unconstrained: *)
        let k_id = GT.Ids.Kind.fresh (Context.get_ctr ctx) in
        let pre_k = Context.make_var ctx Context.prekind (`Free k_id) in
        let k_unguarded = kwithg ctx `Unguarded pre_k in
        let k_guarded = kwithg ctx `Guarded pre_k in
        let k_arg = kwithg ctx `Guarded (Context.make_var ctx Context.prekind (`Arrow(k_unguarded, k_guarded))) in
        kwithg ctx `Guarded (Context.make_var ctx Context.prekind (`Arrow(k_arg, k_guarded)))
and infer_kind_ctor : Context.t -> GT.ctor -> GT.kind GT.var =
  fun ctx ctor ->
    let pk = infer_prekind_ctor ctx ctor in
    Context.make_var ctx Context.kind GT.{
      k_prekind = pk;
      k_guard = Context.make_var ctx Context.guard `Free;
    }
and infer_prekind_ctor : Context.t -> GT.ctor -> GT.prekind GT.var =
  fun ctx ctor ->
    match ctor with
      | `Type _ -> Context.type_v ctx
      | `Row _ -> Context.row_v ctx
and infer_kind_q : Context.t -> GT.quant GT.var -> GT.kind GT.var =
  fun ctx qv ->
    let q = Context.read_var ctx Context.quant qv in
    infer_kind ctx (Lazy.force (q.GT.q_body))
