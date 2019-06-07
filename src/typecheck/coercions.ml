open Ast.Desugared
open Gen_t
open Typecheck_types

open Build_constraint_t

(* Generate coercion types from type annotations.
 *
 * This is based on {MLF-Graph-Infer} section 6, but we do one important
 * thing differently: Instead of *sharing* existential types between the
 * coercion's parameter and result, we map them to flexibly bound bottom
 * nodes in the parameter (as in the paper), but in the result we generate
 * fresh "constant" constructors.
 *
 * The idea is that when we supply a type annotation with an existential
 * in it, we want to *hide* the type from the outside -- this maps closely
 * to sealing in ML module systems. By contrast, the treatment of
 * existentials in the paper is more like "type holes" in some systems --
 * they allow you to specify some of a type annotation, but let the compiler
 * work out the rest. As a concrete example:
 *
 * (fn x. 4) : exist t. t -> t
 *
 * The algorithm in the paper will infer (int -> int), but this code
 * will invent a new constant type t and infer (t -> t).
*)

type env_t = (u_type UnionFind.var) VarMap.t

let gen_kind = function
  | Kind.Type -> `Type
  | Kind.Row -> `Row
  | Kind.Unknown ->
    failwith "BUG: Infer_kind should already have been called"

let rec add_row_to_env: env_t -> u_var -> env_t =
  fun env u ->
    match UnionFind.get u with
    | `Const(_, `Named "<empty>", [], _) | `Free _ -> env
    | `Const(_, `Extend lbl, [head, _; tail, _], _) ->
      add_row_to_env
        (Map.set
           env
           ~key:(Ast.var_of_label lbl)
           ~data:head)
        tail
    | _ ->
      failwith "Illegal row"


(* [gen_type cops b_at env sign ty] generates a graphic type based on [ty].
 *
 * - [cops] is used to generate unification constraints.
 * - monomorphic nodes are bound on [b_at].
 * - [env] is a mapping from type variable names to unification variables; free
 *   variables will be replaced with their values in the map. All free variables
 *   _must_ be contained within the map.
 * - [sign] indicates whether we are in positive or negative position. This is
 *   used to determine the binding flag to use when we see a quantifier. [sign]
 *   is flipped each time we go down the parameter side of a function node.
 *
 * The return value is a unification variable for the root of the type.
 *)
let rec gen_type
  : constraint_ops
  -> bound_target
  -> env_t
  -> sign
  -> 'i Type.t
  -> u_type UnionFind.var
  =
  fun cops b_at env sign ty ->
    let tv = ty_var_at b_at in
    match ty with
    | Type.Annotated (_, _, t) ->
        (* TODO: use the var. *)
        gen_type cops b_at env sign t
    | Type.Opaque _ ->
      failwith
        ("Opaque types should have been removed before generating " ^
         "the constraint graph.")
    | Type.Named (_, s) ->
      UnionFind.make (`Const(tv, `Named s, [], `Type))
    | Type.Fn (_, param, ret) ->
      UnionFind.make
        (fn tv
           (gen_type cops b_at env (flip_sign sign) param)
           (gen_type cops b_at env sign ret))
    | Type.Recur(_, v, body) ->
      let ret = gen_u `Type b_at in
      let ret' = gen_type cops b_at (Map.set env ~key:v ~data:ret) sign body in
      UnionFind.merge (fun _ r -> r) ret ret';
      ret
    | Type.Var (_, v) ->
      Map.find_exn env v
    | Type.Record {r_info = _; r_types; r_values} ->
      let type_row = gen_row cops b_at env sign r_types in
      let env = add_row_to_env env type_row in
      UnionFind.make (
        record tv
          type_row
          (gen_row cops b_at env sign r_values)
      )
    | Type.Union row ->
      UnionFind.make (union tv (gen_row cops b_at env sign row))
    | Type.Quant(_, q, v, k, body) ->
      let ret = gen_u `Type b_at in
      let bound_v =
        UnionFind.make
          (`Free
             ( { ty_id = Gensym.gensym ()
               ; ty_bound = ref
                  { b_ty = get_flag q sign
                  ; b_at = `Ty (lazy ret)
                  }
               }
             , gen_kind k
             ))
      in
      let ret' =
        UnionFind.make (`Quant
                          ( tv
                          , gen_type
                              cops
                              b_at
                              (Map.set env ~key:v ~data:bound_v)
                              sign
                              body
                          )
                       )
      in
      UnionFind.merge (fun _ r -> r) ret ret';
      ret
(* [gen_row] is like [gen_type], but for row variables. *)
and gen_row cops b_at env sign (_, fields, rest) =
  let rest' =
    match rest with
    | Some v -> Map.find_exn env v
    | None -> UnionFind.make (empty (ty_var_at b_at))
  in
  List.fold_right
    fields
    ~init:rest'
    ~f:(fun (lbl, ty) tail ->
        UnionFind.make(
          extend
            (ty_var_at b_at)
            lbl
            (gen_type cops b_at env sign ty)
            tail
        )
      )

let make_coercion_type g ty cops =
  (* Actually make the coercion.
   *
   * General procedure:
   *
   * 1. Infer the kinds within the type.
   * 2. Call [gen_type] twice on ty, with different values for [new_exist];
   *    see the discussion at the top of the file.
   * 3. Generate a function node, and bound the two copies of the type to
   *    it, with the parameter rigid, as described in {MLF-Graph-Infer}.
  *)
  let kinded_ty = Infer_kind.infer VarMap.empty ty in
  fst (Util.fix
         (fun vars ->
            let (param_var, ret_var) = Lazy.force vars in
            UnionFind.make
              ( `Quant
                  ( gen_ty_var g
                  , UnionFind.make (fn (gen_ty_var g) param_var ret_var)
                  )
              )
         )
         (fun root ->
            (* [root] is the final root of the type; it is a quant node, whose child is
             * a function, whose argument and return values will be the two copies of
             * the type in the annotation. The quant node will be the bound of the
             * existentials.
             *)
            let gen sign =
              gen_type cops (`Ty root) VarMap.empty sign kinded_ty
            in
            (gen `Neg, gen `Pos)
         )
      )
