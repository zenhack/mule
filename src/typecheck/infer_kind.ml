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

let rec unify l r = match l, r with
  | `Free n, _ -> occurs_check n r; r
  | _, `Free n -> occurs_check n l; l
  | `Type, `Type -> `Type
  | `Row, `Row -> `Row
  | `Arrow(x, y), `Arrow(x', y') ->
      UnionFind.merge unify x x';
      UnionFind.merge unify y y';
      `Arrow(x, y)

  | _ ->
      MuleErr.(
        throw (TypeError (MismatchedKinds(extract l, extract r)))
      )

let rec walk_type
  : Build_constraint_t.constraint_ops -> k_var VarMap.t -> k_var Type.t -> k_var Type.t =
  fun cops env -> function
    | Type.App(_, f, x) ->
        let f_t = walk_type cops env f in
        let x_t = walk_type cops env x in
        let result_k = to_kvar `Unknown in
        let f_k = Type.get_info f_t in
        let x_k = Type.get_info x_t in
        cops.constrain_kind f_k (UnionFind.make (`Arrow(x_k, result_k)));
        Type.App(result_k, f_t, x_t)
    | Type.TypeLam(_, param, body) ->
        let param_k = to_kvar `Unknown in
        let body_t = walk_type cops (Map.set env ~key:param ~data:param_k) body in
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
    | Type.Opaque k ->
        Type.Opaque k
    | Type.Named (k, s) ->
        Type.Named (k, s)
    | Type.Var(k, v) ->
        (* TODO: proper exception *)
        begin match Map.find env v with
          | Some u_var ->
              cops.constrain_kind k u_var;
              Type.Var(u_var, v)
          | None ->
              MuleErr.bug
                ("unbound variable '" ^ Ast.Var.to_string v
                 ^ "' when inferring kind. This should have been caught"
                 ^ " by the linter."
                )
        end
    | Type.Path(k, v, ls) ->
        let kv = Map.find_exn env v in
        (* The variable itself needs to be of kind `Type, because we're
         * projecting on it as a record. *)
        cops.constrain_kind kv kvar_type;
        (* TODO: I(isd) have a strong feeling that this is missing something here;
         * in particular, we're not doing anything with the kinds of the intermediate
         * labels, which also should have kind type.
         *
         * This whole business is weird because of the way records are mixed in...
        *)
        Type.Path(k, v, ls)
    | Type.Fn(_, Some v, l, r) ->
        let l' = walk_type cops env l in
        let r' = walk_type cops (Map.set env ~key:v ~data:(to_kvar `Type)) r in
        Type.Fn(to_kvar `Type, Some v, l', r')
    | Type.Fn(_, None, l, r) ->
        Type.Fn(to_kvar `Type, None, walk_type cops env l, walk_type cops env r)
    | Type.Recur(_, var, body) ->
        let u_var = kvar_type in
        let body_t = walk_type cops (Map.set env ~key:var ~data:u_var) body in
        cops.constrain_kind u_var (Type.get_info body_t);
        Type.Recur(u_var, var, body_t)
    | Type.Record {r_info = _; r_types; r_values} ->
        let (env, u_types) = collect_assoc_types cops env r_types in
        Type.Record
          { r_info = to_kvar `Type
          (* TODO: make use of the type row. *)
          ; r_types = u_types
          ; r_values = walk_row cops env r_values
          }
    | Type.Union row ->
        Type.Union(walk_row cops env row)
    | Type.Quant(_, q, v, body) ->
        let u_var = gen_k () in
        let body' = walk_type cops (Map.set env ~key:v ~data:u_var) body in
        cops.constrain_kind kvar_type (Type.get_info body');
        Type.Quant(kvar_type, q, v, body')
and walk_row cops env (_, fields, rest) =
  let fields' = List.map fields ~f:(fun (l, t) -> (l, walk_type cops env t)) in
  match rest with
  | None -> (kvar_type, fields', None)
  | Some v ->
      (* TODO: raise a proper error *)
      let u_var = Map.find_exn env v in
      cops.constrain_kind u_var kvar_row;
      (kvar_type, fields', Some v)
and collect_assoc_types cops env (i, field_types, rest) =
  let env =
    List.map field_types ~f:(fun (lbl, t) -> (lbl, Type.get_info t))
    |> List.fold ~init:env ~f:(fun accum (lbl, u) ->
        Map.set
          accum
          ~key:(Ast.var_of_label lbl)
          ~data:u
      )
  in
  (env, walk_row cops env (i, field_types, rest))

let infer = walk_type
