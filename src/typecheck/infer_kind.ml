open Ast.Desugared
open Typecheck_types

let rec to_kvar: Kind.maybe_kind -> k_var = function
  | `Type -> kvar_type
  | `Row -> kvar_row
  | `Unknown -> UnionFind.make (`Free (Gensym.gensym ()))
  | `Arrow(x, y) -> UnionFind.make (`Arrow(to_kvar x, to_kvar y))

let rec extract: u_kind -> Kind.maybe_kind = function
  | `Free _ -> `Unknown
  | `Type -> `Type
  | `Row -> `Row
  | `Arrow(x, y) ->
      `Arrow
        ( extract (UnionFind.get x)
        , extract (UnionFind.get y)
        )

let rec occurs_check: int -> u_kind -> unit =
  fun n -> function
    | `Free m when n = m ->
        MuleErr.(throw (TypeError OccursCheckKind))
    | `Free _ | `Type | `Row -> ()
    | `Arrow(x, y) ->
        occurs_check n (UnionFind.get x);
        occurs_check n (UnionFind.get y)

let rec unify_kind l r = match l, r with
  | `Free n, _ -> occurs_check n r; r
  | _, `Free n -> occurs_check n l; l
  | `Type, `Type -> `Type
  | `Row, `Row -> `Row
  | `Arrow(x, y), `Arrow(x', y') ->
      UnionFind.merge unify_kind x x';
      UnionFind.merge unify_kind y y';
      `Arrow(x, y)

  | _ ->
      MuleErr.(
        throw (TypeError (MismatchedKinds(extract l, extract r)))
      )

let rec walk_type: k_var VarMap.t -> k_var Type.t -> k_var Type.t =
  fun env -> function
    | Type.App(_, f, x) ->
        let f_t = walk_type env f in
        let x_t = walk_type env x in
        let result_k = to_kvar `Unknown in
        let f_k = Type.get_info f_t in
        let x_k = Type.get_info x_t in
        UnionFind.merge unify_kind f_k (UnionFind.make (`Arrow(x_k, result_k)));
        Type.App(result_k, f_t, x_t)
    | Type.TypeLam(_, param, body) ->
        let param_k = to_kvar `Unknown in
        let body_t = walk_type (Map.set env ~key:param ~data:param_k) body in
        Type.TypeLam
          ( UnionFind.make
              (`Arrow
                 ( param_k
                 , Type.get_info body_t
                 )
              )
          , param
          , body_t
          )
    | Type.Annotated(_, _, t) -> walk_type env t
    | Type.Opaque k ->
        Type.Opaque k
    | Type.Named (k, s) ->
        Type.Named (k, s)
    | Type.Var(k, v) ->
        (* TODO: proper exception *)
        begin match Map.find env v with
          | Some u_var ->
              UnionFind.merge unify_kind k u_var;
              Type.Var(u_var, v)
          | None ->
              failwith
                ("BUG: unbound variable '" ^ Ast.Var.to_string v ^ "' when inferring kind."
                 ^ " This should have been caught by the linter."
                )
        end
    | Type.Path(_, v, ls) ->
        let u_var = Map.find_exn env v in
        (* v needs to be of kind `Type, because we're projecting on it as a
         * record. *)
        UnionFind.merge unify_kind u_var (to_kvar `Type);
        Type.Path(u_var, v, ls)
    | Type.Fn(_, (Type.Annotated(_, v, _) as l), r) ->
        let l' = walk_type env l in
        let r' = walk_type (Map.set env ~key:v ~data:(to_kvar `Type)) r in
        Type.Fn
          ( to_kvar `Type
          , Type.Annotated(to_kvar `Type, v, l')
          , r'
          )
    | Type.Fn(_, l, r) ->
        Type.Fn(to_kvar `Type, walk_type env l, walk_type env r)
    | Type.Recur(_, var, body) ->
        let u_var = to_kvar `Type in
        let body_t = walk_type (Map.set env ~key:var ~data:u_var) body in
        UnionFind.merge unify_kind u_var (Type.get_info body_t);
        Type.Recur(u_var, var, body_t)
    | Type.Record {r_info = _; r_types; r_values} ->
        let (env, u_types) = collect_assoc_types env r_types in
        Type.Record
          { r_info = to_kvar `Type
          (* TODO: make use of the type row. *)
          ; r_types = u_types
          ; r_values = walk_row env r_values
          }
    | Type.Union row ->
        Type.Union(walk_row env row)
    | Type.Quant(_, q, v, body) ->
        let u_var = gen_k () in
        let body' = walk_type (Map.set env ~key:v ~data:u_var) body in
        UnionFind.merge unify_kind kvar_type (Type.get_info body');
        Type.Quant(to_kvar `Type, q, v, body')
and walk_row env (_, fields, rest) =
  let fields' = List.map fields ~f:(fun (l, t) -> (l, walk_type env t)) in
  match rest with
  | None -> (to_kvar `Type, fields', None)
  | Some v ->
      (* TODO: raise a proper error *)
      let u_var = Map.find_exn env v in
      UnionFind.merge unify_kind u_var (to_kvar `Row);
      (to_kvar `Type, fields', Some v)
and collect_assoc_types env (i, field_types, rest) =
  let env =
    List.map field_types ~f:(fun (lbl, t) -> (lbl, Type.get_info t))
    |> List.fold ~init:env ~f:(fun accum (lbl, u) ->
        Map.set
          accum
          ~key:(Ast.var_of_label lbl)
          ~data:u
      )
  in
  (env, walk_row env (i, field_types, rest))

let infer = walk_type
