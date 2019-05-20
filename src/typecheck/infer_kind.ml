open Ast.Desugared

let unify_kind l r = match l, r with
  | Kind.Unknown, _ -> r
  | _, Kind.Unknown -> l
  | Kind.Type, Kind.Type -> Kind.Type
  | Kind.Row, Kind.Row -> Kind.Row

  | Kind.Type, Kind.Row
  | Kind.Row, Kind.Type ->
      raise (MuleErr.MuleExn(MuleErr.TypeError(MuleErr.MismatchedKinds(`Row, `Type))))


let rec walk_type env = function
  | Type.Named (_, s) ->
      Type.Named (UnionFind.make(Kind.Unknown), s)
  | Type.Var(_, v) ->
      (* TODO: proper exception *)
      let u_var = Map.find_exn env v in
      UnionFind.merge unify_kind u_var (UnionFind.make Kind.Type);
      Type.Var(u_var, v)
  | Type.Fn(_, l, r) ->
      Type.Fn(UnionFind.make Kind.Type, walk_type env l, walk_type env r)
  | Type.Recur(_, var, body) ->
      let u_var = UnionFind.make Kind.Type in
      Type.Recur(u_var, var, walk_type (Map.set env ~key:var ~data:u_var) body)
  | Type.Record {r_info = _; r_types = _; r_values} ->
      let u_var = UnionFind.make Kind.Type in
      Type.Record
        { r_info = u_var
        (* TODO: make use of the type row. *)
        ; r_types = (UnionFind.make Kind.Row, [], None)
        ; r_values = walk_row env r_values
        }
  | Type.Union row ->
      Type.Union(walk_row env row)
  | Type.Quant(_, q, v, k, body) ->
      let u_var = UnionFind.make k in
      let body' = walk_type (Map.set env ~key:v ~data:u_var) body in
      Type.Quant
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
    | Kind.Unknown -> `Type
    | Kind.Type -> `Type
    | Kind.Row -> `Row
  )
