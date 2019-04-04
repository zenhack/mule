open Ast
open Ast.Desugared
open Gen_t

(* Generate coercion types from type annotations.
 * See {MLF-Graph-Infer} section 6.
 *
 * The general process of constructing a coercion type is as follows:
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

(* Alpha-rename existentially bound vars. *)
let rec rename_ex env = function
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

(* Merge two disjoint maps. Raises an exception if they are not disjoint. *)
let merge_disjoint_exn l r = Map.merge l r ~f:(fun ~key:_ -> function
  | `Left x -> Some x
  | `Right x -> Some x
  | `Both _ -> failwith "Maps not disjoint"
)

let rec collect_exist_vars = function
  (* Collect a list of the existentially bound variables. *)
  | Type.Fn (_, l, r) ->
      merge_disjoint_exn (collect_exist_vars l) (collect_exist_vars r)
  | Type.Recur (_, _, _) ->
      failwith "TODO"
  | Type.Var _ ->
      VarMap.empty
  | Type.Record row -> collect_exist_row row
  | Type.Union row -> collect_exist_row row
  | Type.Quant (k_var, `Exist, v, _, body) ->
      Map.set ~key:v ~data:k_var (collect_exist_vars body)
  | Type.Quant (_, `All, _, _, body) ->
      collect_exist_vars body
and collect_exist_row (_, fields, _) =
  List.fold
    fields
    ~init:VarMap.empty
    ~f:(fun accum (_, v) ->
        merge_disjoint_exn accum (collect_exist_vars v)
    )

type graph_monotype =
  [ `Var of Var.t
  | `Fn of graph_polytype * graph_polytype
  | `Record of graph_row
  | `Union of graph_row
  ]
and graph_polytype =
  { gp_vars: [ `Type | `Row ] VarMap.t
  ; gp_type: graph_monotype
  }
and graph_row =
  ( (Label.t * graph_polytype) list
  * Var.t option
  )

let rec graph_friendly: [ `Type | `Row ] VarMap.t -> 'a Type.t -> graph_polytype =
  (* This function addresses a mismatch between syntactic and graphic types:
    * graphic types don't have separate quantifier nodes, nor are quantifiers
    * ordered. Instead, binding edges point at the type node above which the
    * variables would be bound.
    *
    * This function transforms the type ast into a form where quant nodes cannot
    * appear freely, and several variables are collected together. From there,
    * the graph will be easier to generate.
    *)
  fun acc -> function
  | Type.Quant(_, _, _, Kind.Unknown, _) ->
      failwith "BUG: should have been removed by Kind_infer.infer"
  | Type.Quant(_, _, v, Kind.Type, body) ->
      graph_friendly (Map.set ~key:v ~data:`Type acc) body
  | Type.Quant(_, _, v, Kind.Row, body) ->
      graph_friendly (Map.set ~key:v ~data:`Row acc) body
  | Type.Fn(_, param, ret) ->
      { gp_vars = acc
      ; gp_type = `Fn
          ( graph_friendly VarMap.empty param
          , graph_friendly VarMap.empty ret
          )
      }
  | Type.Recur _ ->
      failwith "TODO"
  | Type.Var (_, v) ->
      { gp_vars = acc
      ; gp_type = `Var v
      }
  | Record row ->
      { gp_vars = acc
      ; gp_type = `Record (graph_friendly_row row)
      }
  | Union row ->
      { gp_vars = acc
      ; gp_type = `Union(graph_friendly_row row)
      }
and graph_friendly_row (_, fields, rest) =
  ( List.map fields ~f:(fun (l, t) -> (l, graph_friendly VarMap.empty t))
  , rest
  )

let make_coercion_type g ty =
  let kinded_ty = Infer_kind.infer VarMap.empty ty in
  let renamed_ty = rename_ex VarMap.empty kinded_ty in
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
      let _ = exist_map in
      failwith "TODO"
    )
  )
