open Ast
open Ast.Desugared
open Gen_t
open Typecheck_types

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
      VarMap.empty
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
  | `Const of (graph_const * graph_polytype list)
  | `Recur of (Var.t * graph_polytype)
  ]
and graph_const =
  [ `Fn
  | `Record
  | `Union
  | `Empty
  | `Extend of Label.t
  ]
and graph_polytype =
  { gp_vars: [ `Type | `Row ] VarMap.t
  ; gp_type: graph_monotype
  }

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
      ; gp_type =
        `Const
          ( `Fn
          , [ graph_friendly VarMap.empty param
            ; graph_friendly VarMap.empty ret
            ]
          )
      }
  | Type.Recur (_, var, body) ->
      { gp_vars = acc
      ; gp_type = `Recur
        ( var
        (* TODO: we don't allow recursive rows, but we should be consistent
         * about checking/enforcing this elsewhere: *)
        , graph_friendly (Map.set ~key:var ~data:`Type acc) body
        )
      }
  | Type.Var (_, v) ->
      { gp_vars = acc
      ; gp_type = `Var v
      }
  | Record row ->
      { gp_vars = acc
      ; gp_type =
          `Const
            ( `Record
            , [graph_friendly_row row]
            )
      }
  | Union row ->
      { gp_vars = acc
      ; gp_type =
          `Const
            ( `Union
            , [graph_friendly_row row]
            )
      }
and graph_friendly_row = function
  | (r, (l, t) :: fs, rest) ->
      let tail = graph_friendly_row (r, fs, rest) in
      { gp_vars = VarMap.empty
      ; gp_type =
        `Const
          ( `Extend l
          , [ graph_friendly VarMap.empty t
            ; tail
            ]
          )
      }
  | (_, [], None) ->
      { gp_vars = VarMap.empty
      ; gp_type = `Const (`Empty, [])
      }
  | (_, [], Some var) ->
      { gp_vars = VarMap.empty
      ; gp_type = `Var var
      }

type env_t = (u_type UnionFind.var) VarMap.t

let rec make_mono: u_kind -> bound_target -> env_t -> graph_monotype -> u_type UnionFind.var =
  fun kind b_at env -> function
  | `Var v ->
      Map.find_exn env v
  | `Recur(v, body) ->
      let ret = gen_u kind b_at in
      let ret' =
        make_poly
          kind
          b_at
          (Map.set env ~key:v ~data:ret)
          body
      in
      UnionFind.merge (fun _ r -> r) ret ret';
      ret
  | `Const(c, args) ->
      let tv = ty_var_at b_at in
      begin match c, args with
      | `Fn, [param; ret] ->
          UnionFind.make
            (fn tv
              (make_poly `Type b_at env param)
              (make_poly `Type b_at env ret))
      | `Record, [row] ->
          UnionFind.make (record tv (make_poly `Row b_at env row))
      | `Union, [row] ->
          UnionFind.make (union tv (make_poly `Row b_at env row))
      | `Empty, [] ->
          UnionFind.make (empty tv)
      | `Extend lbl, [ty; rest] ->
          UnionFind.make
            (extend tv lbl
              (make_poly `Type b_at env ty)
              (make_poly `Row b_at env rest))
      | `Fn, _ | `Record, _ | `Union, _ | `Empty, _ | `Extend _, _ ->
          failwith "BUG: wrong number of args"
      end
and make_poly: u_kind -> bound_target -> env_t -> graph_polytype -> u_type UnionFind.var =
  fun kind b_at env {gp_vars; gp_type} ->
    snd
      ( Util.fix
        (fun parent ->
          let env' = Map.map gp_vars ~f:(fun k -> gen_u k (`Ty parent)) in
          Map.merge env env' ~f:(fun ~key:_ -> function
            | `Left x -> Some x
            | `Right x -> Some x
            | `Both (x, _) -> Some x
          )
        )
        (fun env ->
          make_mono kind b_at (Lazy.force env) gp_type
        )
      )

let make_coercion_type g ty =
  let kinded_ty = Infer_kind.infer VarMap.empty ty in
  let renamed_ty = rename_ex VarMap.empty kinded_ty in
  let exist_vars = collect_exist_vars renamed_ty in
  let graph_ty = graph_friendly VarMap.empty renamed_ty in
  fst (Util.fix
    (fun vars ->
      let (param_var, ret_var) = Lazy.force vars in
      UnionFind.make (fn (gen_ty_var g) param_var ret_var)
    )
    (fun root ->
      (* [root] is the final root of the type; its argument and return values
       * will be the two copies of the type in the annotation, and it will
       * be the bound of the existentials.
       *)
      let exist_map = Map.map exist_vars ~f:(fun k -> gen_u k (`Ty root)) in
      let param = make_poly `Type (`Ty root) exist_map graph_ty in
      let ret = make_poly `Type (`Ty root) exist_map graph_ty in
      let param_bound = (get_tyvar (UnionFind.get param)).ty_bound in
      param_bound := { !param_bound with b_ty = `Rigid };
      (param, ret)
    )
  )
