open Ast.Desugared

let unify_kind l r = match l, r with
  | `Unknown, _ -> r
  | _, `Unknown -> l
  | `Type, `Type -> `Type
  | `Row, `Row -> `Row

  | `Type, `Row
  | `Row, `Type ->
    raise (MuleErr.MuleExn(MuleErr.TypeError(MuleErr.MismatchedKinds(`Row, `Type))))

let rec walk_type env = function
  | Type.TypeLam _ -> failwith "TODO: type lambdas"
  | Type.Annotated(_, _, t) -> walk_type env t
  | Type.Opaque _ ->
    Type.Opaque (UnionFind.make `Unknown)
  | Type.Named (_, s) ->
    Type.Named (UnionFind.make `Unknown, s)
  | Type.Var(_, v) ->
    (* TODO: proper exception *)
    let u_var = Map.find_exn env v in
    UnionFind.merge unify_kind u_var (UnionFind.make `Type);
    Type.Var(u_var, v)
  | Type.Path(_, v, ls) ->
    let u_var = Map.find_exn env v in
    UnionFind.merge unify_kind u_var (UnionFind.make `Type);
    Type.Path(u_var, v, ls)
  | Type.Fn(_, Type.Annotated(_, v, l), r) ->
      let l' = walk_type env l in
      let r' = walk_type (Map.set env ~key:v ~data:(UnionFind.make `Type)) r in
      Type.Fn
        ( UnionFind.make `Type
        , Type.Annotated(UnionFind.make `Type, v, l')
        , r'
        )
  | Type.Fn(_, l, r) ->
    Type.Fn(UnionFind.make `Type, walk_type env l, walk_type env r)
  | Type.Recur(_, var, body) ->
    let u_var = UnionFind.make `Type in
    Type.Recur(u_var, var, walk_type (Map.set env ~key:var ~data:u_var) body)
  | Type.Record {r_info = _; r_types; r_values} ->
    let (env, u_types) = collect_assoc_types env r_types in
    let u_var = UnionFind.make `Type in
    Type.Record
      { r_info = u_var
      (* TODO: make use of the type row. *)
      ; r_types = u_types
      ; r_values = walk_row env r_values
      }
  | Type.Union row ->
    Type.Union(walk_row env row)
  | Type.Quant(_, q, v, k, body) ->
    let u_var = UnionFind.make k in
    let body' = walk_type (Map.set env ~key:v ~data:u_var) body in
    (* XXX: HACK: if the variable name doesn't actually appear in the body
     * of the type, then this will still be 'Unknown'. In this case we can
     * safely default it to 'Type', since it isn't actually used. This is
     * a bit gross though, in that it depends critically on the fact that
     * (for kinds only) we are interleaving constraint building and
     * unification steps.
     *
     * Ideally we'd re-jigger things so that this got dealt with in infer
     * where we default everything else.
     *)
    let k' = match UnionFind.get u_var with
      | `Unknown -> `Type
      | k -> k
    in
    Type.Quant(UnionFind.make `Type, q, v, k', body')
and walk_row env (_, fields, rest) =
  let fields' = List.map fields ~f:(fun (l, t) -> (l, walk_type env t)) in
  match rest with
  | None -> (UnionFind.make `Type, fields', None)
  | Some v ->
    (* TODO: raise a proper error *)
    let u_var = Map.find_exn env v in
    UnionFind.merge unify_kind u_var (UnionFind.make `Row);
    (UnionFind.make `Type, fields', Some v)
and collect_assoc_types env (i, field_types, rest) =
  let env =
    List.map field_types ~f:(fun (lbl, _) -> (lbl, UnionFind.make `Type))
    |> List.fold ~init:env ~f:(fun accum (lbl, u) ->
        Map.set
          accum
          ~key:(Ast.var_of_label lbl)
          ~data:u
      )
  in
  (env, walk_row env (i, field_types, rest))

let infer env ty =
  let env = Map.map env ~f:UnionFind.make in
  let ty' = walk_type env ty in
  Type.map ty' ~f:(fun x ->
      match UnionFind.get x with
      | `Unknown -> `Type
      | `Type -> `Type
      | `Row -> `Row
    )
