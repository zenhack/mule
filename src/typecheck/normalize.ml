open Typecheck_types

(* Reduce the contents of the unification variable to weak head normal form. *)
let rec whnf: u_type UnionFind.var -> u_type UnionFind.var =
  fun uvar -> match UnionFind.get uvar with
    (* Free vars and constant constructors are already in whnf: *)
    | `Free _ | `Const _ -> uvar
    | `Quant(v1, arg1) ->
        (* Adjacent quantifiers should be merged. XXX: not 100% sure what
         * should be done with the bounds here; right now we're just retaining
         * the outermost bound, but I need to think more carefully about what
         * the right thing is.
         *
         * It would at least be sound to raise the two bounds to meet, but I
         * don't know immediately what that would do to completeness.
         *)
        begin match UnionFind.get arg1 with
        | `Quant(_v2, arg2) ->
            UnionFind.merge (fun _ _ ->`Quant(v1, arg2)) uvar arg1;
            whnf uvar
        | _ ->
            uvar
        end
