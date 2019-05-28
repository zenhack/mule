open Ast
open Ast.Desugared
open Gen_t
open Typecheck_types

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

(* [gen_type b_at env ~new_exist ty] generates a graphic type based on [ty].
 *
 * - monomorphic nodes are bound on [b_at].
 * - [new_exist] is used to generate nodes for existentially bound variables;
 *   it is called once per type variable, and passed the kind of that variable.
 * - [env] is a mapping from type variable names to unification variables; free
 *   variables will be replaced with their values in the map. All free variables
 *   _must_ be contained within the map.
 *
 * The return value is a unification variable for the root of the type.
 *)
let rec gen_type
  : bound_target
  -> env_t
  -> new_exist:([ `Type | `Row ] -> u_type UnionFind.var)
  -> 'i Type.t
  -> u_type UnionFind.var
  =
  fun b_at env ~new_exist ty ->
    let tv = ty_var_at b_at in
    match ty with
    | Type.Named (_, s) ->
        UnionFind.make (`Const(tv, `Named s, [], `Type))
    | Type.Fn (_, param, ret) ->
        UnionFind.make
          (fn tv
            (gen_type b_at env ~new_exist param)
            (gen_type b_at env ~new_exist ret))
    | Type.Recur(_, v, body) ->
        let ret = gen_u `Type b_at in
        let ret' = gen_type b_at (Map.set env ~key:v ~data:ret) ~new_exist body in
        UnionFind.merge (fun _ r -> r) ret ret';
        ret
    | Type.Var (_, v) ->
        Map.find_exn env v
    | Type.Record {r_info = _; r_types; r_values} ->
        UnionFind.make (
          record tv
            (gen_row b_at env ~new_exist r_types)
            (gen_row b_at env ~new_exist r_values)
        )
    | Type.Union row ->
        UnionFind.make (union tv (gen_row b_at env ~new_exist row))
    | Type.Quant(_, `All, v, k, body) ->
        let ret = gen_u `Type b_at in
        let bound_v = gen_u (gen_kind k) (`Ty (lazy ret)) in
        let ret' =
          UnionFind.make (`Quant
            ( tv
            , gen_type
                b_at
                (Map.set env ~key:v ~data:bound_v)
                ~new_exist
                body
            )
          )
        in
        UnionFind.merge (fun _ r -> r) ret ret';
        ret
    | Type.Quant(_, `Exist, v, k, body) ->
        gen_type
          b_at
          (Map.set env ~key:v ~data:(new_exist (gen_kind k)))
          ~new_exist
          body
(* [gen_row] is like [gen_type], but for row variables. *)
and gen_row b_at env ~new_exist (_, fields, rest) =
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
          (gen_type b_at env ~new_exist ty)
          tail
      )
    )

let make_coercion_type g ty =
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
      UnionFind.make (fn (gen_ty_var g) param_var ret_var)
    )
    (fun root ->
      (* [root] is the final root of the type; its argument and return values
       * will be the two copies of the type in the annotation, and it will
       * be the bound of the existentials.
       *)
      let gen ~new_exist = gen_type (`Ty root) VarMap.empty ~new_exist kinded_ty in
      let param = gen ~new_exist:(fun k -> gen_u k (`Ty root)) in
      let ret = gen ~new_exist:(fun k ->
        let name = Var.to_string (Gensym.anon_var ()) in
        UnionFind.make (`Const(ty_var_at (`Ty root), `Named name, [], k))
      )
      in
      let param_bound = (get_tyvar (UnionFind.get param)).ty_bound in
      param_bound := { !param_bound with b_ty = `Rigid };
      (param, ret)
    )
  )
