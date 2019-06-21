open Ast.Desugared
open Gen_t
open Typecheck_types

open Build_constraint_t

include Coercions_t

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

let rec gen_kind: Kind.maybe_kind -> u_kind = function
  | `Type -> `Type
  | `Row -> `Row
  | `Arrow (x, y) ->
      `Arrow
        ( UnionFind.make (gen_kind x)
        , UnionFind.make (gen_kind y)
        )
  | `Unknown -> failwith "BUG: infer_kind should have removed this."

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

let rec gen_type
  : constraint_ops
  -> bound_target
  -> env_t
  -> sign
  -> Kind.t Type.t
  -> u_var
  =
  fun cops b_at env sign ty ->
    let tv = ty_var_at b_at in
    match ty with
    | Type.App(_, f, x) ->
        let f' = gen_type cops b_at env sign f in
        let x' = gen_type cops b_at env sign x in
        UnionFind.make(apply tv f' (Type.get_info f) x' (Type.get_info x))
    | Type.TypeLam _ -> failwith "TODO: TypeLam"
    | Type.Annotated (_, _, t) ->
        gen_type cops b_at env sign t
    | Type.Opaque _ ->
      failwith
        ("Opaque types should have been removed before generating " ^
         "the constraint graph.")
    | Type.Named (_, s) ->
      UnionFind.make (`Const(tv, `Named s, [], `Type))
    | Type.Fn (_, param, ret) ->
        let param' =
          gen_type cops b_at env (flip_sign sign) param
        in
        let env' = match param with
          | Type.Annotated(_, v, _) ->
              Map.set env ~key:v ~data:param'
          | _ ->
              env
        in
        let ret' =
          gen_type cops b_at env' sign ret
        in
        UnionFind.make (fn tv param' ret')
    | Type.Recur(_, v, body) ->
      let ret = gen_u `Type b_at in
      let ret' = gen_type cops b_at (Map.set env ~key:v ~data:ret) sign body in
      UnionFind.merge (fun _ r -> r) ret ret';
      ret
    | Type.Var (_, v) ->
        Map.find_exn env v
    | Type.Path(_, v, ls) ->
        let rec go t = function
          | [] -> t
          | [lbl] ->
            let ret = gen_u `Type b_at in
            let record =
              UnionFind.make
                (record (ty_var_at b_at)
                   (UnionFind.make (extend (ty_var_at b_at) lbl ret (gen_u `Row b_at)))
                   (gen_u `Row b_at))
            in
            cops.constrain_unify record t;
            ret
          | (l :: ls) ->
            let l' = gen_u `Type b_at in
            let ret = go l' ls in
            let record =
              UnionFind.make
                (record (ty_var_at b_at)
                   (gen_u `Row b_at)
                   (UnionFind.make (extend (ty_var_at b_at) l l' (gen_u `Row b_at))))
            in
            cops.constrain_unify record t;
            ret
        in
        go (Map.find_exn env v) ls
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
                              (`Ty (lazy bound_v))
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

let make_coercion_type env g ty cops =
  (* General procedure:
   *
   * 1. Infer the kinds within the type.
   * 2. Call [gen_type] twice on ty, with different values for [new_exist];
   *    see the discussion at the top of the file.
   * 3. Generate a function node, and bound the two copies of the type to
   *    it, with the parameter rigid, as described in {MLF-Graph-Infer}.
  *)
  (* FIXME: this precludes us from having named types for anything not of kind
   * [Type]; find a better solution:
   *)
  let kind_env = Map.map env ~f:(fun _ -> `Type) in
  let kinded_ty = Infer_kind.infer kind_env ty in
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
              gen_type cops (`Ty root) env sign kinded_ty
            in
            (gen `Neg, gen `Pos)
         )
      )
