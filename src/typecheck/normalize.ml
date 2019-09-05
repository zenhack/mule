open Typecheck_types

let rec is_bound_above {ty_bound; _} parent =
  let {ty_id; _} = get_tyvar (UnionFind.get parent) in
  match (!ty_bound).b_at with
  | `G _ -> false
  | `Ty uv ->
      let uv = Lazy.force uv in
      let tv = get_tyvar (UnionFind.get uv) in
      if ty_id = tv.ty_id then
        false
      else
        is_bound_above tv parent

(* Reduce the contents of the unification variable to normal form. *)
let rec nf: u_type UnionFind.var -> u_type UnionFind.var =
  fun uvar ->
  match UnionFind.get uvar with
  | `Const(_, `Named "<apply>", [f, _; x, _], _) ->
      apply uvar (nf f) (nf x)
  | `Quant(tv, arg) ->
      UnionFind.set (`Quant(tv, nf arg)) uvar;
      uvar
  | `Const(tv, `Extend lbl, [h, hk; t, tk], k) ->
      let t = nf_row (LabelSet.singleton lbl) t in
      UnionFind.set
        (`Const(tv, `Extend lbl, [nf h, hk; t, tk], k))
        uvar;
      uvar
  | _ ->
      uvar
and nf_row: LabelSet.t -> u_type UnionFind.var -> u_type UnionFind.var =
  fun lbls uvar ->
  match UnionFind.get uvar with
  | `Const(tv, `Extend lbl, [h, hk; t, tk], k) ->
      if Set.mem lbls lbl then
        nf_row lbls t
      else
        begin
          let t' = nf_row (Set.add lbls lbl) t in
          let ret = UnionFind.make (`Const(Gen_t.clone_ty_var tv, `Extend lbl, [nf h, hk; t', tk], k)) in
          (if UnionFind.equal t t' then
            UnionFind.merge (fun _ r -> r) uvar ret);
          ret
        end
  | _ ->
      uvar
and apply appvar f x =
  match UnionFind.get f with
  | `Quant(_, arg) ->
      (* FIXME/XXX: What do we do with the q-node? what if things are bound on it? *)
      apply appvar arg x
  | `Const(tv, `Named "<lambda>", [p, _; r, _], _) ->
      let (tv, p, r) =
        if is_bound_above tv appvar then
          copy_subgraph appvar (tv, p, r)
        else
          (tv, p, r)
      in
      let new_bound = !((get_tyvar (UnionFind.get appvar)).ty_bound) in
      tv.ty_bound := new_bound;
      let x_tv = get_tyvar (UnionFind.get x) in
      x_tv.ty_bound := new_bound;
      let r_tv = get_tyvar (UnionFind.get r) in
      r_tv.ty_bound := new_bound;
      UnionFind.merge (fun _ r -> r) p x;
      UnionFind.merge (fun _ r -> r) appvar r;
      r
  | _ ->
      appvar
and copy_subgraph appvar (tv, p, r) =
  let copied: u_type UnionFind.var Lazy.t IntMap.t ref = ref IntMap.empty in
  let rec go uv =
    let ty = UnionFind.get uv in
    let tv = get_tyvar ty in
    match Map.find !copied tv.ty_id with
    | Some n -> Lazy.force n
    | None when is_bound_above tv appvar -> uv
    | None ->
        begin match (!(tv.ty_bound)).b_at with
          | `G _ -> failwith "impossible"
          | `Ty parent_u ->
              let new_parent =
                Lazy.force parent_u
                |> UnionFind.get
                |> get_tyvar
                |> (fun {ty_id; _} -> Map.find_exn !copied ty_id)
              in
              let new_tv =
                { ty_id = Gensym.gensym ()
                ; ty_bound = ref
                      { b_at = `Ty new_parent
                      ; b_ty = (!(tv.ty_bound)).b_ty
                      }
                }
              in
              let ret = lazy (
                begin match ty with
                  | `Free(_, k) -> UnionFind.make (`Free(new_tv, k))
                  | `Quant(_, arg) -> UnionFind.make (`Quant(new_tv, go arg))
                  | `Const(_, tag, args, k) ->
                      UnionFind.make
                        (`Const
                           ( new_tv
                           , tag
                           , List.map args ~f:(fun (t, k) -> (go t, k))
                           , k
                           )
                        )
                end
              )
              in
              copied := Map.set !copied ~key:tv.ty_id ~data:ret;
              Lazy.force ret
        end
  in
  let p = go p in
  let r = go r in
  ( { ty_id = Gensym.gensym ()
    ; ty_bound = ref (!(tv.ty_bound))
    }
  , p
  , r
  )

let pair: u_var -> u_var -> (u_var * u_var) =
  let rec go l r =
    match UnionFind.get l, UnionFind.get r with
    | `Quant _, `Quant _ -> (l, r)
    | `Quant _, t ->
        let tv' =
          { ty_id = Gensym.gensym ()
          ; ty_bound = ref (!((get_tyvar t).ty_bound))
          }
        in
        (l, UnionFind.make (`Quant(tv', r)))
    | _, `Quant _ -> go r l
    | _ -> (l, r)
  in
  fun l r -> go (nf l) (nf r)
