open Typecheck_types

(* make sure the argument is a quantifier. If not, wrap it in a quantifier.
 * We bound it on the same node, though the bound doesn't matter since it's
 * inert. *)
let ensure_quant: u_type UnionFind.var -> u_type UnionFind.var =
  fun uvar -> match UnionFind.get uvar with
    | `Quant _ ->
        uvar
    | arg ->
        let tv = Gen_t.ty_var_at ((get_u_bound arg).b_at) in
        UnionFind.make(`Quant(tv, uvar))


(* Reduce the contents of the unification variable to weak head normal form. *)
let rec whnf: u_type UnionFind.var -> u_type UnionFind.var =
  fun uvar -> match UnionFind.get uvar with
    (* Free vars are already in whnf: *)
    | `Free _ -> uvar
    | `Const(v, c, args, k) ->
        (* Constant constructors must always have quantifiers for children: *)
        UnionFind.set
          (`Const(v, c, List.map args ~f:(fun (arg, k) -> (ensure_quant arg, k)), k))
          uvar;
        uvar
    | `Quant(v1, arg1) ->
        (* Adjacent quantifiers should be merged. XXX: not 100% sure what
         * should be done with the bounds here; right now we're just retaining
         * the outermost bound, but I need to think more carefully about what
         * the right thing is.
         *)
        begin match UnionFind.get arg1 with
        | `Quant(_v2, arg2) ->
            UnionFind.merge (fun _ _ ->`Quant(v1, arg2)) uvar arg1;
            whnf uvar
        | _ ->
            uvar
        end
