open Typecheck_types
open Gen_t
open Ast

(* Normalize a row, staring with [extend b_at lbl head tail].
 *
 * This drops duplicate labels, and sorts what's left. The end
 * of the extend chain is left in-place.
 *
 * A critical invariant is that extend nodes are always inert,
 * so we can ignore the bounds in the other elements of the list.
 *)
let whnf_extend b_at lbl head tail =
  let rec collect_fields var = match UnionFind.get var with
    | `Const(_, `Extend lbl, [head, `Type; tail, `Row], _) ->
        let rest, tail = collect_fields tail in
        ( (lbl, head) :: rest
        , tail
        )
    | _ -> ([], var)
  in
  let (fields, tail) = collect_fields tail in
  let fields = (lbl, head) :: fields in
  let rec remove_duplicates seen = function
    | [] -> []
    | ((lbl, ty) :: xs) ->
        if Set.mem seen lbl then
          remove_duplicates seen xs
        else
          (lbl, ty) :: remove_duplicates (Set.add seen lbl) xs
  in
  let de_duped = remove_duplicates LabelSet.empty fields in
  let sorted =
    List.sort
      de_duped
      ~compare:(fun (l, _) (r, _) -> Label.compare l r)
  in
  let rec rebuild = function
    | [] -> tail
    | (lbl, head) :: xs ->
        UnionFind.make
          (extend
            (ty_var_at b_at)
            lbl
            head
            (rebuild xs))
  in
  UnionFind.get (rebuild sorted)

let whnf ty = match ty with
  | `Free _ -> ty
  | `Const({ty_bound; _}, c, args, _) ->
      begin match c, args with
      | `Extend lbl, [head, `Type; tail, `Row] ->
          let {b_at; _} = !ty_bound in
          whnf_extend b_at lbl head tail
      | `Extend _, _ ->
          failwith "BUG: malformed extend"
      | _ -> ty
      end
