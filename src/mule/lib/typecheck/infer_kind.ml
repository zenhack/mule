module GT = Graph_types
module C = Constraint_t

let kwithg ctx guard pkv = Context.make_var ctx Context.kind GT.{
    k_prekind = pkv;
    k_guard = Context.make_var ctx Context.guard guard;
  }

let mkpk ctx pk = Context.make_var ctx Context.prekind pk

let rec infer_kind : Context.t -> GT.typ GT.var -> GT.kind GT.var =
  fun ctx t ->
    let t = Context.read_var ctx Context.typ t in
    match t with
    | `Free tv -> tv.GT.tv_kind
    | `Ctor (_, ctor) -> infer_kind_ctor ctx ctor
    | `Poison _ ->
        kwithg ctx `Poison (mkpk ctx `Poison)
    | `GetField _ ->
        (* Make sure the arguement and result share a guard *)
        let k = Context.make_var ctx Context.kind GT.{
            k_prekind = mkpk ctx `Type;
            k_guard = Context.make_var ctx Context.guard `Free;
          }
        in
        kwithg ctx `Free (mkpk ctx (`Arrow(k, k)))
    | `Lambda(_, p, r) ->
        let k_p = infer_kind_q ctx p in
        let k_r = infer_kind_q ctx r in
        kwithg ctx `Free (mkpk ctx (`Arrow(k_p, k_r)))
    | `Apply(_, f, arg) ->
        let k_f = infer_kind_q ctx f in
        let k_arg = infer_kind_q ctx arg in
        let k_ret = kwithg ctx `Free (mkpk ctx (`Free(GT.Ids.Kind.fresh (Context.get_ctr ctx)))) in
        let k_f' = kwithg ctx `Free (mkpk ctx (`Arrow(k_arg, k_ret))) in
        Context.constrain ctx (`UnifyKind C.{
            unify_kind_sub = k_f;
            unify_kind_super = k_f';
            unify_kind_why = `Apply;
          });
        k_ret
    | `Fix _ ->
        (* (unguarded 'k -> guarded 'k) -> guarded 'k,
           where the arrows' guards are unconstrained: *)
        let k_id = GT.Ids.Kind.fresh (Context.get_ctr ctx) in
        let pre_k = mkpk ctx (`Free k_id) in
        let k_unguarded = kwithg ctx `Unguarded pre_k in
        let k_guarded = kwithg ctx `Guarded pre_k in
        let k_arg = kwithg ctx `Guarded (mkpk ctx (`Arrow(k_unguarded, k_guarded))) in
        kwithg ctx `Guarded (mkpk ctx (`Arrow(k_arg, k_guarded)))
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
    | `Type tc ->
        constrain_prekind_type_ctor ctx tc;
        Context.type_v ctx
    | `Row rc ->
        constrain_prekind_row_ctor ctx rc;
        Context.row_v ctx
and constrain_prekind_row_ctor ctx = function
  | `Empty -> ()
  | `Extend (_, h, t) ->
      let hk = infer_kind_q ctx h in
      let tk = infer_kind_q ctx t in
      Context.constrain ctx
        (`UnifyKind C.{
          unify_kind_why = `CtorArg (`Extend `Head);
          unify_kind_super = kwithg ctx `Free (mkpk ctx `Type);
          unify_kind_sub = hk;
        });
      Context.constrain ctx
        (`UnifyKind C.{
          unify_kind_why = `CtorArg (`Extend `Tail);
          unify_kind_super = kwithg ctx `Free (mkpk ctx `Row);
          unify_kind_sub = tk;
        })
and constrain_prekind_type_ctor ctx = function
  | `Fn (p, r) ->
      let pk = infer_kind_q ctx p in
      let rk = infer_kind_q ctx r in
      Context.constrain ctx
        (`UnifyKind C.{
          unify_kind_why = `CtorArg (`Fn `Param);
          unify_kind_super = kwithg ctx `Free (mkpk ctx `Type);
          unify_kind_sub = pk;
        });
      Context.constrain ctx
        (`UnifyKind C.{
          unify_kind_why = `CtorArg (`Fn `Result);
          unify_kind_super = kwithg ctx `Free (mkpk ctx `Type);
          unify_kind_sub = rk;
        })
  | `Record (t, v) ->
      let tk = infer_kind_q ctx t in
      let vk = infer_kind_q ctx v in
      Context.constrain ctx
        (`UnifyKind C.{
          unify_kind_why = `CtorArg (`Record `Types);
          unify_kind_super = kwithg ctx `Free (mkpk ctx `Row);
          unify_kind_sub = tk;
        });
      Context.constrain ctx
        (`UnifyKind C.{
          unify_kind_why = `CtorArg (`Record `Values);
          unify_kind_super = kwithg ctx `Free (mkpk ctx `Row);
          unify_kind_sub = vk;
        })
  | `Union r ->
      let k = infer_kind_q ctx r in
      Context.constrain ctx
        (`UnifyKind C.{
          unify_kind_why = `CtorArg `Union;
          unify_kind_super = kwithg ctx `Free (mkpk ctx `Row);
          unify_kind_sub = k;
        })
  | `Const _ ->
      ()
and infer_kind_q : Context.t -> GT.quant GT.var -> GT.kind GT.var =
  fun ctx qv ->
    let q = Context.read_var ctx Context.quant qv in
    infer_kind ctx (Lazy.force (q.GT.q_body))
