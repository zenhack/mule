open Ast.Desugared
open Gen_t

let make_coercion_type cops env g ty =
  (* We construct the type of a coercion as follows:
   *
   * 1. Alpha-rename the existentially-bound variables within the type.
   *    This way we don't have to worry about shadowing in later steps.
   * 2. Collect the names of existentially-bound variables.
   * 3. Generate a unification variable for each existential, and store
   *    them in a map.
   * 4. Walk over the type twice, generating two constraint graphs for it
   *    which share only the nodes for existential variables (looked up
   *    in the map we generated.
   * 5. Make a function node.
   * 6. Bind each of the copies to the function node. The parameter will
   *    be bound rigidly, and the result flexibly.
   * 7. Bind the existentials to the new function node.
   *)
  let rec rename_ex env = function
      (* Alpha-rename existentially bound vars. *)
      | Type.Fn(i, l, r) ->
          Type.Fn(i, rename_ex env l, rename_ex env r)
      | Type.Recur(i, v, body) ->
          Type.Recur(i, v, rename_ex (Map.remove env v) body)
      | Type.Var (i, v) ->
          begin match Map.find env v with
            | Some v' -> Type.Var (i, v')
            | None -> Type.Var (i, v)
          end
      | Type.Record row -> Type.Record (rename_ex_row env row)
      | Type.Union row -> Type.Union (rename_ex_row env row)
      | Type.Quant(i, `All, v, kind, body) ->
          Type.Quant(i, `All, v, kind, rename_ex (Map.remove env v) body)
      | Type.Quant(i, `Exist, v, kind, body) ->
          let v' = Gensym.anon_var () in
          Type.Quant(i, `Exist, v', kind, rename_ex (Map.set ~key:v ~data:v' env) body)
    and rename_ex_row env (i, fields, rest) =
      ( i
      , List.map fields ~f:(fun (l, v) -> (l, rename_ex env v))
      , Option.map rest ~f:(fun r -> match Map.find env r with
            | None -> r
            | Some v -> v
        )
      )
  in
  let merge_disjoint ~key:_ = function
    (* Function to pass to Map.merge, which assumes that the maps are disjoint
     * and just combines the results naively. *)
    | `Left x -> Some x
    | `Right x -> Some x
    | `Both _ -> failwith "impossible"
  in
  let rec collect_exist_vars = function
    (* Collect a list of the existentially bound variables. *)
    | Type.Fn (_, l, r) ->
        Map.merge ~f:merge_disjoint (collect_exist_vars l) (collect_exist_vars r)
    | Type.Recur (_, _, _) ->
        failwith "TODO"
    | Type.Var _ ->
        Map.empty (module Ast.Var)
    | Type.Record row -> collect_exist_row row
    | Type.Union row -> collect_exist_row row
    | Type.Quant (k_var, `Exist, v, _, body) ->
        Map.set ~key:v ~data:k_var (collect_exist_vars body)
    | Type.Quant (_, `All, _, _, body) ->
        collect_exist_vars body
  and collect_exist_row (_, fields, _) =
    List.fold
      fields
      ~init:(Map.empty (module Ast.Var))
      ~f:(fun accum (_, v) ->
          Map.merge ~f:merge_disjoint accum (collect_exist_vars v)
      )
  in
  let rec graph_friendly acc = function
    (* This function addresses a mismatch between syntactic and graphic types:
      * graphic types don't have separate quantifier nodes, nor are quantifiers
      * ordered. Instead, binding edges point at the type node above which the
      * variables would be bound.
      *
      * This function transforms the type ast into a form where there are no
      * Quant nodes, and all variables are collected on type nodes. From there,
      * the graph will be easier to generate.
      *)
    | Type.Quant(_, _, _, Kind.Unknown, _) ->
        failwith "BUG: should have been removed by Kind_infer.infer"
    | Type.Quant(_, _, v, Kind.Type, body) ->
        graph_friendly (`Type v :: acc) body
    | Type.Quant(_, _, v, Kind.Row, body) ->
        graph_friendly (`Row v :: acc) body
    | Type.Fn(_, param, ret) ->
        `Fn(List.rev acc, graph_friendly [] param, graph_friendly [] ret)
    | Type.Recur _ ->
        failwith "TODO"
    | Type.Var (_, v) ->
        `Var (List.rev acc, v)
    | Record row ->
        `Record (List.rev acc, graph_friendly_row row)
    | Union row ->
        `Union (List.rev acc, graph_friendly_row row)
  and graph_friendly_row (_, fields, rest) =
    ( List.map fields ~f:(fun (l, t) -> (l, graph_friendly [] t))
    , rest
    )
  in
  let kinded_ty = Infer_kind.infer (Map.empty (module Ast.Var)) ty in
  let renamed_ty = rename_ex (Map.empty (module Ast.Var)) kinded_ty in
  let exist_vars = collect_exist_vars renamed_ty in
  fst (Util.fix
    (fun vars ->
      let (param_var, ret_var) = Lazy.force vars in
      UnionFind.make
        (`Fn
          ( gen_ty_var g
          , param_var
          , ret_var
          )
        )
    )
    (fun root ->
      (* [root] is the final root of the type; its argument and return values
       * will be the two copies of the type in the annotation, and it will
       * be the bound of the existentials.
       *)
      (* TODO(FIXME?): we have a weird hack in place elsewhere where we bind the
       * scope of record and union types to the root of their row -- do
       * we need to do the same here?
       *)
      let exist_map = Map.map exist_vars ~f:(function
        | `Type -> `Type (gen_u (`Ty root))
        | `Row -> `Row (gen_u (`Ty root))
      ) in
      let _ = (cops, env, exist_map) in
      failwith "TODO"
    )
  )
