
(* This module implements the 'expand' operation,
   from {MLF-Graph-Infer} section 3.1 *)

module GT = Graph_types
module C = Constraint_t

type is_root =
  | Root of GT.g_node
  | NotRoot of GT.quant GT.var

let make_bound : Context.t -> is_root -> GT.bound_flag -> GT.bound GT.var =
  fun ctx is_root flag ->
    Context.make_var ctx Context.bound (
      match is_root with
      | Root g -> {
          b_target = `G g;
          b_flag = `Flex
        }
      | NotRoot q -> {
          b_target = `Q q;
          b_flag = flag;
        }
    )


let rec walk_q ctx qv ~g ~is_root ~inst_c ~seen =
  let q = Context.read_var ctx Context.quant qv in
  Seen.get seen.Expand_reduce.seen_q q.q_id (fun () ->
    let ctr = Context.get_ctr ctx in
    let
      GT.{
        b_flag = old_flag;
        b_target = q_parent;
      } = Context.read_var ctx Context.bound q.q_bound
    in
    let q_in_constraint_interior =
      Expand_reduce.bound_under seen ctx ~limit:(`G g) ~target:q_parent
    in
    let q_bound =
      if q_in_constraint_interior then
        make_bound ctx is_root old_flag
      else
        Context.make_var ctx Context.bound {
          b_target = `G g;
          b_flag = `Flex;
        }
    in
    let q_id = GT.Ids.Quant.fresh ctr in
    let rec q_body = lazy (
      let tv = Lazy.force q.q_body in
      if q_in_constraint_interior then
        walk_ty ctx
          ~tv
          ~root:(Lazy.force root)
          ~g
          ~inst_c
          ~seen
      else
        begin
          let tv_id = GT.Ids.Type.fresh ctr in
          Context.make_var ctx Context.typ (`Free {
            tv_id;
            tv_merged = Set.singleton (module GT.Ids.Type) tv_id;
            tv_bound = make_bound ctx (NotRoot (Lazy.force qv')) `Flex;
            tv_kind = Infer_kind.infer_kind ctx tv;
          })
        end
    )
    and root = lazy (match is_root with
      | Root _ -> Lazy.force qv'
      | NotRoot qroot -> qroot
    )
    and qv' = lazy (Context.make_var ctx Context.quant {
        q_id;
        q_merged = Set.singleton (module GT.Ids.Quant) q_id;
        q_bound;
        q_body;
      })
    in
    ignore (Lazy.force q_body);
    if not q_in_constraint_interior then
      Context.constrain ctx (`Unify {
          unify_why = `InstanceLeaf inst_c;
          unify_sub = Lazy.force qv';
          unify_super = qv;
        });
    Lazy.force qv'
  )
and walk_ty ctx ~tv ~root ~g ~inst_c ~seen =
  let ty = Context.read_var ctx Context.typ tv in
  Seen.get seen.seen_ty (GT.typ_id ty) (fun () ->
    let walk_q' qv = walk_q ctx qv ~is_root:(NotRoot root) ~g ~inst_c ~seen in
    let id' = GT.Ids.Type.fresh (Context.get_ctr ctx) in
    match ty with
    | `Free ftv ->
        let t_bound = Context.read_var ctx Context.bound ftv.tv_bound in
        let bound = make_bound ctx (NotRoot root) t_bound.b_flag in
        let tv' = Context.make_var ctx Context.typ (`Free {
            tv_id = id';
            tv_merged = Set.singleton (module GT.Ids.Type) id';
            tv_bound = bound;
            tv_kind = ftv.tv_kind;
          })
        in
        if not (Expand_reduce.bound_under seen ctx ~limit:(`G g) ~target:t_bound.b_target) then
          begin
            (* HACK: we need to unify the two type variables, but
               our unification constraints act on Q-nodes. So, we create
               two fresh, inert Q nodes, point one at each type var, and
               then unify the Q nodes. We should probably refactor to
               allow just putting the constraint directly on the type
               vars. *)
            let fresh_q body =
              let q_id = GT.Ids.Quant.fresh (Context.get_ctr ctx) in
              Context.make_var ctx Context.quant {
                q_id;
                q_merged = Set.singleton (module GT.Ids.Quant) q_id;
                q_bound = Context.make_var ctx Context.bound {
                    b_target = `G g;
                    b_flag = `Flex;
                  };
                q_body = lazy body;
              }
            in
            Context.constrain ctx (`Unify C.{
                unify_why = `InstanceLeaf inst_c;
                unify_super = fresh_q tv;
                unify_sub = fresh_q tv';
              })
          end;
        tv'
    | `Poison _ -> tv
    | `Apply(_, f, arg) ->
        Context.make_var ctx Context.typ (`Apply(id', walk_q' f, walk_q' arg))
    | `Lambda(_, p, r)  ->
        Context.make_var ctx Context.typ (`Lambda(id', walk_q' p, walk_q' r))
    | `Ctor(_, ctor) ->
        Context.make_var ctx Context.typ (`Ctor(id', GT.map_ctor ~f:walk_q' ctor))
 )

let expand ctx ~g ~at ~inst_c =
  let qv = Lazy.force (GT.GNode.get g) in
  walk_q ctx qv ~g:at ~is_root:(Root at) ~inst_c ~seen:(Expand_reduce.make_seen ())
