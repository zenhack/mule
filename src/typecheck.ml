module S = Set.Make(Ast.Var)
module Env = Map.Make(Ast.Var)

open Ast.Desugared
open Gensym
open OrErr


(* The type of values associated with unification variables *)
type u_mono =
  | Type of tyvar
  | Fn of (tyvar * u_mono UnionFind.var * u_mono UnionFind.var)
  | Record of (tyvar * u_row UnionFind.var)
  | Union of (tyvar * u_row UnionFind.var)
and u_row =
  | Extend of (Ast.Label.t * u_mono UnionFind.var * u_row UnionFind.var)
  | Empty
  | Row of int
and bound_ty = (* Rigid | *) Flex
and bound = (bound_ty * poly)
and poly =
  | Bottom
  (* | Mono of u_mono
  | All of ((int * bound) list * poly)
  *)
and tyvar = (int * bound ref)

let gen_ty_var () =
  (gensym (), ref (Flex, Bottom))

let gen_ty_u () =
  UnionFind.make (Type (gen_ty_var ()))

let rec unify l r =
  match l, r with
  (* same type variable. *)
  | Type (lv, _), Type (rv, rb) when lv = rv ->
      Ok (Type (rv, rb))

  (* Top level type constructor that matches. In the
   * literature, these are treated uniformly and opaquely.
   * We have a case for each just because (a) we have a
   * so few of them them, and (b) we have to deal with
   * different kinds of argument variables. In principle we
   * could factor out the commonalities, and maybe we will
   * eventually, but for now there just isn't that much. *)
  | (Fn (i, ll, lr), Fn (_, rl, rr)) ->
      UnionFind.merge unify ll rl
      >>= fun l' -> UnionFind.merge unify lr rr
      |>> fun r' -> Fn (i, l', r')
  | (Record (i, row_l), Record(_, row_r)) ->
      UnionFind.merge unify_row row_l row_r
      |>> fun row_ret -> Record (i, row_ret)
  | (Union (i, row_l), Union(_, row_r)) ->
      UnionFind.merge unify_row row_l row_r
      |>> fun row_ret -> Union(i, row_ret)

  (* Type constructor mismatches. we could have a catchall,
   * but this means we don't forget a case. it would be nice
   * to refactor so we don't have to list every combination
   * though. *)
  | Fn _, Record _ | Fn _, Union _
  | Record _, Fn _ | Record _, Union _
  | Union _, Fn _ | Union _, Record _ ->
      Err Error.TypeMismatch

  | Type _, t | t, Type _ -> Ok t
and unify_row l r =
  match l, r with
  | (Empty, Empty) -> Ok Empty
  | (Extend (l_lbl, l_ty, l_rest), Extend (r_lbl, r_ty, r_rest)) ->
      if l_lbl = r_lbl then
        UnionFind.merge unify l_ty r_ty
        >>= fun ret_ty -> UnionFind.merge unify_row l_rest r_rest
        |>> fun ret_rest -> Extend (l_lbl, ret_ty, ret_rest)
      else
        UnionFind.merge unify_row
          r_rest
          (UnionFind.make (Extend(l_lbl, l_ty, UnionFind.make (Row (gensym())))))
        >>= fun _ ->
        UnionFind.merge unify_row
          l_rest
          (UnionFind.make (Extend(r_lbl, r_ty, UnionFind.make (Row (gensym())))))
        |>> fun rest ->
          Extend(l_lbl, l_ty, rest)

  | (Row _, r) -> Ok r
  | (l, Row _) -> Ok l
  | (Extend _, Empty) -> Err Error.TypeMismatch
  | (Empty, Extend _) -> Err Error.TypeMismatch

let rec walk env = function
  | Expr.Var v ->
      Ok (Env.find v env)
  | Expr.Lam (param, body) ->
      let paramVar = gen_ty_u () in
      walk (Env.add param paramVar env) body
      |>> fun retVar -> UnionFind.make (Fn (gen_ty_var (), paramVar, retVar))
  | Expr.App (f, arg) ->
      walk env f
      >>= fun fVar -> walk env arg
      >>= fun argVar ->
        let retVar = gen_ty_u () in
        UnionFind.merge unify
          fVar
          (UnionFind.make (Fn (gen_ty_var (), argVar, retVar)))
      |>> fun _ -> retVar
  | Expr.Record fields ->
      walk_fields env (UnionFind.make Empty) (RowMap.bindings fields)
      |>> fun row -> UnionFind.make (Record (gen_ty_var (), row))
  | Expr.GetField (e, lbl) ->
      walk env e
      >>= fun tyvar ->
      let rowVar = UnionFind.make (Row (gensym ())) in
      let recVar = UnionFind.make (Record (gen_ty_var (), rowVar)) in
      UnionFind.merge unify
        recVar
        tyvar
      >>= fun _ ->
      let tailVar = UnionFind.make (Row (gensym ())) in
      let fieldVar = gen_ty_u () in
      UnionFind.merge unify_row
          rowVar
          (UnionFind.make (Extend(lbl, fieldVar, tailVar)))
      |>> fun _ ->
          fieldVar
  | Expr.Update (r, updates) ->
      walk env r
      >>= fun origVar ->
        let tailVar = UnionFind.make (Row (gensym())) in
        walk_fields env tailVar updates
      >>= fun updateVar ->
        UnionFind.merge unify
          origVar
          (UnionFind.make (Record (gen_ty_var (), tailVar)))
      |>> fun _ -> UnionFind.make (Record (gen_ty_var (), updateVar))
  | Expr.Ctor (lbl, param) ->
      walk env param
      |>> fun paramVar -> UnionFind.make
        ( Union
          ( gen_ty_var ()
          , UnionFind.make
            ( Extend
                ( lbl
                , paramVar
                , UnionFind.make (Row (gensym ()))
                )
            )
          )
        )
  | Expr.Match {cases; default} when RowMap.is_empty cases ->
      begin match default with
        | None -> Err EmptyMatch
        | Some (Some paramVar, body) ->
            walk env (Expr.Lam (paramVar, body))
        | Some (None, body) ->
            walk env (Expr.Lam (Ast.Var.of_string "_", body))
      end
  | Expr.Match {cases; default} ->
      let final = match default with
        | None -> UnionFind.make Empty
        | Some _ -> UnionFind.make (Row (gensym ()))
      in
      walk_match env final (RowMap.bindings cases)
      |>> fun (rowVar, bodyVar) ->
          UnionFind.make
            ( Fn
                ( gen_ty_var ()
                , UnionFind.make (Union(gen_ty_var (), rowVar))
                , bodyVar
                )
            )
and walk_match env final = function
  | [] -> Ok (final, gen_ty_u ())
  | ((lbl, (var, body)) :: rest) ->
      let ty = gen_ty_u () in
      walk (Env.add var ty env) body
      >>= fun bodyVar -> walk_match env final rest
      >>= fun (row, body') -> UnionFind.merge unify bodyVar body'
      |>> fun bvar ->
        ( UnionFind.make (Extend(lbl, ty, row))
        , bvar
        )
and walk_fields env final = function
  | [] -> Ok final
  | ((lbl, ty) :: fs) ->
      walk env ty
      >>= fun lblVar -> walk_fields env final fs
      |>> fun tailVar ->
        UnionFind.make (Extend(lbl, lblVar, tailVar))

let ivar i = Ast.Var.of_string ("t" ^ string_of_int i)

let maybe_add_rec i vars ty =
  let myvar = ivar i in
  if S.mem myvar vars then
    ( S.remove myvar vars
    , Type.Recur(i, myvar, ty)
    )
  else
    (vars, ty)

let rec add_rec_binders ty =
  match ty with
  | Type.Var (_, v) ->
      ( S.singleton v
      , ty
      )
  | Type.Recur(i, v, t) ->
      let (vs, ts) = add_rec_binders t in
      ( S.remove (ivar i) vs
      , Type.Recur(i, v, ts)
      )
  | Type.Fn (i, f, x) ->
      let (fv, ft) = add_rec_binders f in
      let (xv, xt) = add_rec_binders x in
      maybe_add_rec i (S.union fv xv) (Type.Fn(i, ft, xt))
  | Type.Record(i, fields, rest) ->
      let (vars, ret) = row_add_rec_binders i fields rest in
      maybe_add_rec i vars (Type.Record ret)
  | Type.Union(i, ctors, rest) ->
      let (vars, ret) = row_add_rec_binders i ctors rest in
      maybe_add_rec i vars (Type.Union ret)
  | Type.All(i, bound, body) ->
      let (vars, body') = add_rec_binders body in
      maybe_add_rec i vars (Type.All(i, bound, body'))
and row_add_rec_binders i fields rest =
  let row_var = match rest with
    | Some v -> S.singleton v
    | None -> S.empty
  in
  let fields_vars = List.map
    (fun (lbl, ty) -> (lbl, add_rec_binders ty))
    fields
  in
  let vars = List.fold_left
    (fun accum (_, (vars, _)) -> S.union accum vars)
    row_var
    fields_vars
  in
  let fields' = List.map (fun (lbl, (_, ty)) -> (lbl, ty)) fields_vars in
  (vars, (i, fields', rest))
let add_rec_binders ty =
  snd (add_rec_binders ty)

(* Extract a type from a (solved) unification variable. *)
let rec get_var_type env = function
  | Type (i, _) -> Type.Var (i, (ivar i))
  | Fn ((i, b), f, x) ->
      if S.mem (ivar i) env then
        get_var_type env (Type (i, b))
      else
        let env' = S.add (ivar i) env in
        Fn
          ( i
          , get_var_type env' (UnionFind.get f)
          , get_var_type env' (UnionFind.get x)
          )
  | Record ((i, _), fields) ->
      let (fields, rest) =
        get_var_row (S.add (ivar i) env) (UnionFind.get fields)
      in
      Type.Record (i, fields, rest)
  | Union ((i, _), ctors) ->
      let (ctors, rest) =
        get_var_row (S.add (ivar i) env) (UnionFind.get ctors)
      in
      Type.Union (i, ctors, rest)
and get_var_row env = function
  | Row i -> ([], Some (ivar i))
  | Empty -> ([], None)
  | Extend (lbl, ty, rest) ->
      let (fields, rest) = get_var_row env (UnionFind.get rest) in
      ( ( lbl
        , get_var_type env (UnionFind.get ty)
        )
        :: fields
      , rest
      )
let get_var_type uvar =
  UnionFind.get uvar
    |> get_var_type S.empty
    |> add_rec_binders

let typecheck expr =
  walk Env.empty expr
  |>> get_var_type
