
let unify_kind l r = match l, r with
  | Kind.Unknown, _ -> r
  | _, Kind.Unknown -> l
  | Kind.Type, Kind.Type -> Kind.Type
  | Kind.Row, Kind.Row -> Kind.Row

  | Kind.Type, Kind.Row
  | Kind.Row, Kind.Type ->
      raise (MuleErr.TypeError(MuleErr.MismatchedKinds(l, r)))


let rec walk_type env = function
  | Fn(_, l, r) ->
      Fn(UnionFind.make Kind.Type, walk_type env l, walk_type env r)
  | Recur(_, var, body) ->
      let u_var = UnionFind.make Kind.Type in
      Recur(u_var, var, walk_type (Map.set env ~key:var ~data:u_var) body)
  | Record row ->
      Record(walk_row row)
  | Union row ->
      Union(walk_row row)
  | Quant(_, q, v, k, body) ->
      let u_var = UnionFind.make k in
      let body' = walk_type (Map.set env ~key:v ~data:u_var) body in
      Quant
        ( UnionFind.make Kind.Type
        , q
        , v
        , UnionFind.get u_var
        , body'
        )
and walk_row env (_, fields, rest) =
  let fields' = List.map fields ~f:(fun (l, t) -> (l, walk_type env t)) in
  match rest with
    | None -> (UnionFind.make Kind.Type, fields', None)
    | Some v ->
        (* TODO: raise a proper error *)
        let u_var = Map.find_exn env v in
        UnionFind.merge unify_kind u_var (UnionFind.make Kind.Row);
        (UnionFind.make Kind.Type, fields', Some v)

let infer env ty =
  let env = Map.map env ~f:UnionFind.make in
  let ty' = walk_type env ty in
  Type.map ty' ~f:(fun x ->
    match UnionFind.get x with
    | Kind.Unknown -> Kind.Type
    | k -> k
  )
