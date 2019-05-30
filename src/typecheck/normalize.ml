open Typecheck_types

(* Reduce the contents of the unification variable to weak head normal form. *)
let whnf: u_type UnionFind.var -> u_type UnionFind.var =
  (* Right now this is a no-op, but once we add higher-kinds/type operators,
   * we'll do beta reduction here.
   *)
  fun uvar -> uvar

let rec pair: u_var -> u_var -> (u_var * u_var) =
    fun l r ->
      let l, r = whnf l, whnf r in
      match UnionFind.get l, UnionFind.get r with
      | `Quant _, `Quant _ -> (l, r)
      | `Quant _, t ->
        let tv' =
          { ty_id = Gensym.gensym ()
          ; ty_bound = ref (!((get_tyvar t).ty_bound))
          }
        in
        (l, UnionFind.make (`Quant(tv', r)))
      | _, `Quant _ ->
        let (r, l) = pair r l in
        (l, r)
      | _ -> (l, r)
